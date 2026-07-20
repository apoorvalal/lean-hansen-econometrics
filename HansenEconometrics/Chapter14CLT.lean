import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ConditionalExpectation
import HansenEconometrics.Chapter14MDS
import HansenEconometrics.Chapter14TimeSeries
import HansenEconometrics.Chapter14Mixing
import HansenEconometrics.ErgodicTheory.PathShift
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 14: Time Series — the central limit theorem layer (analytic core)

This file will hold the Chapter 14 central limit theorem layer. The CLT arguments of Hansen
§14 (the martingale-difference CLT 14.11 and the mixing CLT 14.15) all run through the
characteristic function `MeasureTheory.charFun` together with the classical estimate on how
fast the complex exponential is approximated by the partial sums of its power series. This
first pass lands that unconditional analytic core; the probabilistic CLT bundles that consume
it, and which depend on repository modules, arrive in a later work package that extends this
file.

## Main declarations

* `ProbabilityTheory.norm_cexp_sub_sum_le_pow_div_factorial` — the standard Taylor bound for
  the complex exponential along the imaginary axis: for `x : ℝ` and `n : ℕ`,
  `‖exp (x·I) - ∑ k < n, (x·I)^k / k!‖ ≤ |x|^n / n!`. Proved by induction on `n` through the
  fundamental theorem of calculus.
* `ProbabilityTheory.norm_cexp_sub_sum_le_two_mul_pow_div_factorial` — the companion bound, in
  successor form: `‖exp (x·I) - ∑ k < n+1, (x·I)^k / k!‖ ≤ 2·|x|^n / n!`. This is the estimate
  that survives when `|x|` is large; it follows from the previous lemma at index `n` by the
  triangle inequality.
* `ProbabilityTheory.norm_cexp_sub_sum_min_bound` — the combined min-form estimate used in CLT
  arguments (Billingsley eq. (26.4), Durrett Lemma 3.3.19): for `1 ≤ n`,
  `‖exp (x·I) - ∑ k < n, (x·I)^k / k!‖ ≤ min (|x|^n / n!) (2·|x|^(n-1) / (n-1)!)`.
* `ProbabilityTheory.norm_cexp_sub_taylor_three`, `ProbabilityTheory.norm_cexp_sub_taylor_two`
  — the second- and first-order specializations actually invoked by the CLT proofs,
  `‖exp (x·I) - (1 + x·I - x²/2)‖ ≤ min (|x|^3 / 6) (x^2)` and
  `‖exp (x·I) - (1 + x·I)‖ ≤ min (|x|^2 / 2) (2·|x|)`.

These lemmas are stated for the complex exponential and are Mathlib-shaped and upstreamable
(they carry no repository dependency); on upstreaming they would naturally live in the
`Complex` namespace rather than `ProbabilityTheory`.
-/

open MeasureTheory

namespace ProbabilityTheory

/-- The `n`-th Taylor remainder of the imaginary-axis exponential:
`cexpTaylorRem n x = exp (x·I) - ∑ k < n, (x·I)^k / k!`. Scaffolding for the CLT estimates. -/
private noncomputable def cexpTaylorRem (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I) -
    ∑ k ∈ Finset.range n, ((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)

/-- The remainder is an antiderivative of `I` times the previous remainder:
`d/dx cexpTaylorRem (n+1) = I · cexpTaylorRem n`. This is the recursion that drives the
inductive Taylor bound. -/
private lemma hasDerivAt_cexpTaylorRem (n : ℕ) (x : ℝ) :
    HasDerivAt (cexpTaylorRem (n + 1)) (Complex.I * cexpTaylorRem n x) x := by
  -- Derivative of `y ↦ (y : ℂ) * I`.
  have hu : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I x := by
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    simpa using h1.mul_const Complex.I
  -- Derivative of the exponential term.
  have hexp : HasDerivAt (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
      (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x := hu.cexp
  -- Derivative of the partial sum, summand by summand.
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), ((y : ℂ) * Complex.I) ^ k / (k.factorial : ℂ))
      (∑ k ∈ Finset.range (n + 1),
        ((k : ℂ) * ((x : ℂ) * Complex.I) ^ (k - 1) * Complex.I) / (k.factorial : ℂ)) x :=
    HasDerivAt.fun_sum (fun k _ => (hu.fun_pow k).div_const _)
  -- Reindex the derivative of the partial sum into `I` times the previous partial sum.
  have hS : (∑ k ∈ Finset.range (n + 1),
        ((k : ℂ) * ((x : ℂ) * Complex.I) ^ (k - 1) * Complex.I) / (k.factorial : ℂ))
      = Complex.I * ∑ k ∈ Finset.range n, ((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h1 : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have h2 : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    field_simp
  -- Assemble the derivative and rewrite it into the target form.
  have hderiv := hexp.sub hsum
  rw [hS] at hderiv
  have hval : Complex.exp ((x : ℂ) * Complex.I) * Complex.I
        - Complex.I * ∑ k ∈ Finset.range n, ((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)
      = Complex.I * cexpTaylorRem n x := by
    simp only [cexpTaylorRem]
    ring
  rw [hval] at hderiv
  exact hderiv

/-- **Taylor bound for the imaginary-axis exponential, nonnegative half-line.** For `0 ≤ x`,
`‖cexpTaylorRem n x‖ ≤ x^n / n!`. Proved by induction on `n` via the fundamental theorem of
calculus; keeping `x` nonnegative sidesteps all sign bookkeeping in the integral estimate. -/
private lemma norm_cexpTaylorRem_le_of_nonneg :
    ∀ (n : ℕ) {x : ℝ}, 0 ≤ x → ‖cexpTaylorRem n x‖ ≤ x ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro x _
    simp only [cexpTaylorRem, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I x)
  | succ n ih =>
    intro x hx
    -- Fundamental theorem of calculus on `[0, x]`.
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt (cexpTaylorRem (n + 1)) (Complex.I * cexpTaylorRem n y) y :=
      fun y _ => hasDerivAt_cexpTaylorRem n y
    have hcont0 : Continuous (fun y : ℝ => cexpTaylorRem n y) := by
      simp only [cexpTaylorRem]; fun_prop
    have hint : IntervalIntegrable (fun y : ℝ => Complex.I * cexpTaylorRem n y) volume 0 x :=
      (continuous_const.mul hcont0).intervalIntegrable 0 x
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have h0 : cexpTaylorRem (n + 1) 0 = 0 := by
      simp [cexpTaylorRem, Finset.sum_range_succ']
    rw [h0, sub_zero] at hFTC
    rw [← hFTC]
    calc ‖∫ y in (0 : ℝ)..x, Complex.I * cexpTaylorRem n y‖
        ≤ ∫ y in (0 : ℝ)..x, ‖Complex.I * cexpTaylorRem n y‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx
      _ = ∫ y in (0 : ℝ)..x, ‖cexpTaylorRem n y‖ := by
          simp only [norm_mul, Complex.norm_I, one_mul]
      _ ≤ ∫ y in (0 : ℝ)..x, y ^ n / (n.factorial : ℝ) := by
          apply intervalIntegral.integral_mono_on hx
          · exact hcont0.norm.intervalIntegrable 0 x
          · exact Continuous.intervalIntegrable (by fun_prop) 0 x
          · exact fun y hy => ih hy.1
      _ = x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [intervalIntegral.integral_div, integral_pow,
            zero_pow (Nat.succ_ne_zero n), sub_zero, div_div]
          congr 1
          rw [Nat.factorial_succ]
          push_cast
          ring

/-- The remainder along the negative half-axis is the complex conjugate of the remainder along
the positive half-axis: `cexpTaylorRem n (-x) = conj (cexpTaylorRem n x)`. Consequently its norm
is even in `x`, which lifts the nonnegative bound to all of `ℝ`. -/
private lemma cexpTaylorRem_neg (n : ℕ) (x : ℝ) :
    cexpTaylorRem n (-x) = (starRingEnd ℂ) (cexpTaylorRem n x) := by
  have hcore : ((-x : ℝ) : ℂ) * Complex.I = (starRingEnd ℂ) ((x : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  simp only [cexpTaylorRem, map_sub, map_sum, map_div₀, map_pow, map_natCast,
    ← Complex.exp_conj, hcore]

/-- **Taylor bound for the imaginary-axis exponential (first branch).** For all `x : ℝ` and
`n : ℕ`, `‖exp (x·I) - ∑ k < n, (x·I)^k / k!‖ ≤ |x|^n / n!`. This is the standard Taylor
estimate on the characteristic function of a real random variable (Billingsley eq. (26.4)). -/
theorem norm_cexp_sub_sum_le_pow_div_factorial (n : ℕ) (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        ∑ k ∈ Finset.range n, ((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖
      ≤ |x| ^ n / (n.factorial : ℝ) := by
  change ‖cexpTaylorRem n x‖ ≤ |x| ^ n / (n.factorial : ℝ)
  have hnorm_even : ‖cexpTaylorRem n x‖ = ‖cexpTaylorRem n |x|‖ := by
    rcases abs_choice x with h | h
    · rw [h]
    · rw [h, cexpTaylorRem_neg, RCLike.norm_conj]
  rw [hnorm_even]
  exact norm_cexpTaylorRem_le_of_nonneg n (abs_nonneg x)

/-- **Taylor bound for the imaginary-axis exponential (second branch), successor form.** For all
`x : ℝ` and `n : ℕ`, `‖exp (x·I) - ∑ k < n+1, (x·I)^k / k!‖ ≤ 2·|x|^n / n!`. This bound, unlike
the first branch, does not decay in `n` but stays controlled for large `|x|`; it is obtained by
peeling the top term off the `(n+1)`-term partial sum and applying the first branch at `n`. -/
theorem norm_cexp_sub_sum_le_two_mul_pow_div_factorial (n : ℕ) (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        ∑ k ∈ Finset.range (n + 1), ((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖
      ≤ 2 * |x| ^ n / (n.factorial : ℝ) := by
  have hsplit : cexpTaylorRem (n + 1) x
      = cexpTaylorRem n x - ((x : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) := by
    simp only [cexpTaylorRem, Finset.sum_range_succ]
    ring
  have hterm : ‖((x : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖ = |x| ^ n / (n.factorial : ℝ) := by
    simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  change ‖cexpTaylorRem (n + 1) x‖ ≤ 2 * |x| ^ n / (n.factorial : ℝ)
  rw [hsplit]
  calc ‖cexpTaylorRem n x - ((x : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖
      ≤ ‖cexpTaylorRem n x‖ + ‖((x : ℂ) * Complex.I) ^ n / (n.factorial : ℂ)‖ := norm_sub_le _ _
    _ ≤ |x| ^ n / (n.factorial : ℝ) + |x| ^ n / (n.factorial : ℝ) := by
        rw [hterm]; gcongr; exact norm_cexp_sub_sum_le_pow_div_factorial n x
    _ = 2 * |x| ^ n / (n.factorial : ℝ) := by ring

/-- **Combined min-form Taylor bound (Billingsley eq. (26.4) / Durrett Lemma 3.3.19).** For
`1 ≤ n` and all `x : ℝ`,
`‖exp (x·I) - ∑ k < n, (x·I)^k / k!‖ ≤ min (|x|^n / n!) (2·|x|^(n-1) / (n-1)!)`.
This is the estimate consumed by the Lindeberg/martingale-difference CLT arguments. -/
theorem norm_cexp_sub_sum_min_bound {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        ∑ k ∈ Finset.range n, ((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ)‖
      ≤ min (|x| ^ n / (n.factorial : ℝ)) (2 * |x| ^ (n - 1) / ((n - 1).factorial : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine le_min (norm_cexp_sub_sum_le_pow_div_factorial (m + 1) x) ?_
  exact norm_cexp_sub_sum_le_two_mul_pow_div_factorial m x

/-- **Second-order specialization** used directly by CLT arguments (the `n = 3` form). Since
`∑ k < 3, (x·I)^k / k! = 1 + x·I - x²/2`, this reads
`‖exp (x·I) - (1 + x·I - x²/2)‖ ≤ min (|x|^3 / 6) (x^2)`. -/
theorem norm_cexp_sub_taylor_three (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖
      ≤ min (|x| ^ 3 / 6) (x ^ 2) := by
  have hsum : (1 : ℂ) + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2
      = ∑ k ∈ Finset.range 3, ((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one,
      Nat.factorial_two, Nat.cast_ofNat]
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hsum]
  refine le_min ?_ ?_
  · have h := norm_cexp_sub_sum_le_pow_div_factorial 3 x
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rwa [h6] at h
  · have h := norm_cexp_sub_sum_le_two_mul_pow_div_factorial 2 x
    have h2 : 2 * |x| ^ 2 / ((Nat.factorial 2 : ℕ) : ℝ) = x ^ 2 := by
      rw [Nat.factorial_two]; push_cast; rw [sq_abs]; ring
    rwa [h2] at h

/-- **First-order specialization** (the `n = 2` form). Since `∑ k < 2, (x·I)^k / k! = 1 + x·I`,
this reads `‖exp (x·I) - (1 + x·I)‖ ≤ min (|x|^2 / 2) (2·|x|)`. -/
theorem norm_cexp_sub_taylor_two (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I)‖
      ≤ min (|x| ^ 2 / 2) (2 * |x|) := by
  have hsum : (1 : ℂ) + (x : ℂ) * Complex.I
      = ∑ k ∈ Finset.range 2, ((x : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [Nat.factorial_one]
  rw [hsum]
  refine le_min ?_ ?_
  · have h := norm_cexp_sub_sum_le_pow_div_factorial 2 x
    have h2 : |x| ^ 2 / ((Nat.factorial 2 : ℕ) : ℝ) = |x| ^ 2 / 2 := by
      rw [Nat.factorial_two]; norm_num
    rwa [h2] at h
  · have h := norm_cexp_sub_sum_le_two_mul_pow_div_factorial 1 x
    have h1 : 2 * |x| ^ 1 / ((Nat.factorial 1 : ℕ) : ℝ) = 2 * |x| := by
      rw [Nat.factorial_one]; simp
    rwa [h1] at h

/-!
## Hansen Theorem 14.11 — the martingale-difference-sequence central limit theorem

This section lands the CLT for a stationary, ergodic, square-integrable martingale difference
sequence (Hansen Theorem 14.11) in the *bundle-conditional* form dictated by the honest-gap
analysis: the full characteristic-function induction that drives an MDS CLT is not assemblable
from the pinned Mathlib (there is no conditional-`charFun` telescoping and no triangular-array
machinery), so the single analytic input — pointwise convergence of the characteristic function
of the normalized partial sums to the Gaussian characteristic function — is carried as a field
of the hypothesis bundle `MDSCLTConditions`. Everything downstream of that field is fully
formalized here: `MDSCLTConditions.central_limit` consumes the field through Mathlib's Lévy
continuity theorem (`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`) and pins the
limit down to `gaussianReal 0 σ²` via `ProbabilityTheory.charFun_gaussianReal`.

A future work package that discharges the analytic field would prove exactly
`charFun_tendsto` (the conditional-`charFun` induction, with the ergodic theorem normalizing the
conditional variances) and thereby construct the bundle from Hansen's four genuine hypotheses.
-/

section MDSCentralLimit

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℤ m} {u : ℤ → Ω → ℝ}

/-- **Hansen Theorem 14.11 hypotheses (assumption bundle).**

The hypotheses of Hansen's martingale-difference-sequence central limit theorem, packaged in
the repository's `ScoreCLTConditions` pattern. The process `u : ℤ → Ω → ℝ` is:

* `toIsMDS` — a martingale difference sequence relative to the information filtration `ℱ`
  (`ProbabilityTheory.IsMDS`: adapted, integrable, `E[uₜ | ℱₜ₋₁] = 0`);
* `stationary` — strictly stationary (`ProbabilityTheory.IsStrictlyStationary`);
* `ergodic` — ergodic (`ProbabilityTheory.IsErgodicProcess`, i.e. the path-space shift is
  ergodic for the path law);
* `memLp_two` — square-integrable at every time, `MemLp (uₜ) 2 P`.

These four fields are Hansen's actual assumptions. The final field is the analytic core:

* `charFun_tendsto` — the characteristic function of the law of the normalized partial sum
  `(√n)⁻¹ ∑_{t < n} u₍ₜ₊₁₎` converges pointwise to the characteristic function
  `s ↦ exp(-σ² s² / 2)` of the centered Gaussian with variance `σ² = Var[u₁]`.

This last field is *not derivable* from the first four in the pinned Mathlib — it stands in for
the conditional-characteristic-function induction plus the ergodic normalization of conditional
variances, neither of which is available. A full proof of Theorem 14.11 would derive
`charFun_tendsto` from the first four fields and so *construct* this bundle; the endpoint
`MDSCLTConditions.central_limit` below then delivers the convergence-in-distribution conclusion
unconditionally from the bundle. The partial sum is indexed as `∑_{t ∈ range n} u₍ₜ₊₁₎`, i.e.
`u₁ + ⋯ + uₙ`, so the natural normalizing variance is `Var[u₁]` (equal to `Var[uₜ]` for every
`t` by stationarity). -/
structure MDSCLTConditions (ℱ : Filtration ℤ m) (u : ℤ → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] extends IsMDS ℱ u P where
  /-- The process is strictly stationary. -/
  stationary : IsStrictlyStationary u P
  /-- The process is ergodic (the path-space shift is ergodic for the path law). -/
  ergodic : IsErgodicProcess u P
  /-- Each `uₜ` is square-integrable. -/
  memLp_two : ∀ t, MemLp (u t) 2 P
  /-- **The analytic core (bundle-conditional).** The characteristic function of the normalized
  partial sum `(√n)⁻¹ ∑_{t < n} u₍ₜ₊₁₎` converges pointwise to `s ↦ exp(-Var[u₁]·s²/2)`, the
  characteristic function of `N(0, Var[u₁])`. -/
  charFun_tendsto : ∀ s : ℝ,
    Filter.Tendsto
      (fun n : ℕ => charFun
        (P.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)) s)
      Filter.atTop (nhds (Complex.exp (-(variance (u 1) P : ℂ) * (s : ℂ) ^ 2 / 2)))

omit [IsProbabilityMeasure P] in
/-- The characteristic function of the Gaussian limit `N(0, Var[u₁])` evaluated at `s` equals
the analytic target `exp(-Var[u₁]·s²/2)` of `MDSCLTConditions.charFun_tendsto`. This is the
`charFun_gaussianReal` identification, with the nonnegative-variance coercion
`((Var[u₁]).toNNReal : ℝ) = Var[u₁]` discharged; it covers the degenerate case `Var[u₁] = 0`
(where `gaussianReal 0 0 = δ₀` and both sides are the constant `1`) with no side hypothesis. -/
private theorem charFun_gaussianReal_variance_eq (s : ℝ) :
    charFun (gaussianReal 0 (variance (u 1) P).toNNReal) s
      = Complex.exp (-(variance (u 1) P : ℂ) * (s : ℂ) ^ 2 / 2) := by
  rw [charFun_gaussianReal]
  congr 1
  have hv : ((variance (u 1) P).toNNReal : ℝ) = variance (u 1) P :=
    Real.coe_toNNReal _ (variance_nonneg (u 1) P)
  push_cast [hv]
  ring

/-- **Hansen Theorem 14.11 — martingale-difference-sequence central limit theorem
(bundle endpoint).**

From the `MDSCLTConditions` bundle, the normalized partial sums `(√n)⁻¹ ∑_{t < n} u₍ₜ₊₁₎`
converge in distribution to a `N(0, Var[u₁])` limit, phrased in the repository's Chapter 7
convergence idiom: against any reference random variable `Z` on any probability space with
`HasLaw Z (gaussianReal 0 (Var[u₁]).toNNReal) P'`. The proof consumes the bundle's analytic
field `charFun_tendsto` through Mathlib's Lévy continuity theorem
(`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`) and identifies the limit with
the Gaussian via `charFun_gaussianReal_variance_eq`. No `0 < Var[u₁]` hypothesis is needed: the
degenerate case is handled by `charFun_gaussianReal` (`gaussianReal 0 0 = δ₀`). -/
theorem MDSCLTConditions.central_limit {Ω' : Type*} {m' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (h : MDSCLTConditions ℱ u P)
    (hZ : HasLaw Z (gaussianReal 0 (variance (u 1) P).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)
      Filter.atTop Z (fun _ => P) P' where
  forall_aemeasurable n := by
    refine AEMeasurable.const_mul ?_ _
    exact Finset.aemeasurable_fun_sum _ fun i _ => (h.integrable ((i : ℤ) + 1)).aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun s => ?_
    rw! [hZ.map_eq]
    simpa [charFun_gaussianReal_variance_eq] using h.charFun_tendsto s

end MDSCentralLimit

/-!
## Hansen Theorem 14.11, multivariate form — the vector martingale-difference CLT

Theorems 14.30/14.35 (least-squares asymptotic normality) consume the martingale-difference CLT
in its *vector* form: for a stationary ergodic square-integrable martingale difference sequence
`u : ℤ → Ω → (k → ℝ)`, the normalized partial sums converge to a multivariate Gaussian with the
process's asymptotic covariance matrix. This section lands that vector CLT in the repository's
Cramér–Wold face, matching the Chapter 7 idiom
(`scoreEuclidean_sampleCrossMoment_tendstoInDistribution_multivariateGaussian`): the vector limit
is obtained from the scalar `MDSCLTConditions.central_limit` along every fixed linear projection
`a ⬝ u`, glued by `cramerWold_tendstoInDistribution`.

The single missing analytic input — pointwise characteristic-function convergence — is carried
exactly as in the scalar bundle, one scalar `MDSCLTConditions` per projection direction (the
`proj` field). The asymptotic covariance matrix is an explicit field `covMat` tied to the process
through the projected-variance identity `Var[a ⬝ u₁] = a' (covMat) a`, the multivariate analogue
of the scalar bundle's `Var[u₁]`; its positive semidefiniteness (not implied by the quadratic-form
identity, which pins only the symmetric part) is carried as the field `posSemidef`.
-/

section MDSCentralLimitVec

open Matrix

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℤ m} {k : Type*} [Fintype k] [DecidableEq k] {u : ℤ → Ω → (k → ℝ)}

/-- **Hansen Theorem 14.11 hypotheses, multivariate form (assumption bundle).**

The vector-process analogue of `MDSCLTConditions`, for a `(k → ℝ)`-valued process
`u : ℤ → Ω → (k → ℝ)`. Following the repository's Cramér–Wold design for multivariate limits, the
bundle carries one scalar `MDSCLTConditions` per linear projection direction rather than a single
vector hypothesis:

* `proj` — for every direction `a : k → ℝ`, the scalar projected process `t ↦ a ⬝ uₜ` is a
  stationary ergodic square-integrable martingale difference sequence whose normalized partial
  sums have Gaussian-converging characteristic function (a full `MDSCLTConditions` bundle). This
  is the multivariate analytic core, carried projectionwise exactly as the scalar bundle carries
  its `charFun_tendsto`.

The asymptotic covariance is explicit:

* `covMat` — the asymptotic covariance matrix `Σ`;
* `posSemidef` — `Σ` is positive semidefinite. This is *not* implied by `variance_proj` (a
  quadratic form pins only the symmetric part of `covMat` and gives only nonnegativity), and it is
  required for `multivariateGaussian 0 covMat` to be a genuine Gaussian law;
* `variance_proj` — `Σ` is tied to the process through the projected variances: for every `a`,
  `Var[a ⬝ u₁] = a' Σ a`. This is the vector analogue of the scalar bundle's normalizing variance
  `Var[u₁]`, and it is what makes each projection of `multivariateGaussian 0 covMat` the exact
  scalar Gaussian limit that `MDSCLTConditions.central_limit` produces.

A consumer (e.g. Theorem 14.30) holds a `MDSCLTConditionsVec` and obtains the vector limit in one
application of `MDSCLTConditionsVec.central_limit`; a future full proof of Theorem 14.11 would
construct this bundle from the scalar bundles along each direction. -/
structure MDSCLTConditionsVec (ℱ : Filtration ℤ m) (u : ℤ → Ω → (k → ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] where
  /-- Every scalar projection `a ⬝ u` satisfies the scalar Theorem 14.11 hypothesis bundle. -/
  proj : ∀ a : k → ℝ, MDSCLTConditions ℱ (fun t ω => u t ω ⬝ᵥ a) P
  /-- The asymptotic covariance matrix `Σ`. -/
  covMat : Matrix k k ℝ
  /-- `Σ` is positive semidefinite (as a genuine covariance matrix). -/
  posSemidef : covMat.PosSemidef
  /-- `Σ` is tied to the projected variances: `Var[a ⬝ u₁] = a' Σ a` for every direction `a`. -/
  variance_proj : ∀ a : k → ℝ, variance (fun ω => u 1 ω ⬝ᵥ a) P = a ⬝ᵥ (covMat *ᵥ a)

/-- Coordinatewise a.e.-measurability of a vector process carrying a `MDSCLTConditionsVec` bundle:
the `i`-th coordinate `uₜ(·)ᵢ` is a.e.-measurable, recovered from the integrability of the
projection along the `i`-th standard basis vector `Pi.single i 1`. -/
private lemma MDSCLTConditionsVec.aemeasurable_apply
    (h : MDSCLTConditionsVec ℱ u P) (t : ℤ) (i : k) :
    AEMeasurable (fun ω => u t ω i) P := by
  have hmeas : AEMeasurable (fun ω => u t ω ⬝ᵥ Pi.single i (1 : ℝ)) P :=
    ((h.proj (Pi.single i 1)).integrable t).aemeasurable
  refine hmeas.congr (ae_of_all _ fun ω => ?_)
  simp only [dotProduct_single, mul_one]

/-- **Hansen Theorem 14.11 — multivariate martingale-difference-sequence central limit theorem
(bundle endpoint).**

From the vector bundle `MDSCLTConditionsVec`, the normalized vector partial sums
`(√n)⁻¹ • ∑_{t < n} u₍ₜ₊₁₎` converge in distribution to a `N(0, Σ)` limit on
`EuclideanSpace ℝ k`, phrased in the repository's Chapter 7 convergence idiom: against any
reference random variable `Z` on any probability space with
`HasLaw Z (multivariateGaussian 0 Σ) P'`. The proof is the Cramér–Wold reduction of
`scoreEuclidean_sampleCrossMoment_tendstoInDistribution_multivariateGaussian`: for each direction
`a = t.ofLp`, the projected process `a ⬝ u` is a scalar bundle (`h.proj a`) whose
`MDSCLTConditions.central_limit` delivers the one-dimensional CLT, with limit
`gaussianReal 0 (Var[a ⬝ u₁]).toNNReal = gaussianReal 0 (a' Σ a).toNNReal`, matching the projection
of `multivariateGaussian 0 Σ` (`hasLaw_multivariateGaussian_zero_dotProduct`); the
projectionwise limits are then assembled by `cramerWold_tendstoInDistribution`. -/
theorem MDSCLTConditionsVec.central_limit {Ω' : Type*} {m' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → EuclideanSpace ℝ k}
    (h : MDSCLTConditionsVec ℱ u P)
    (hZ : HasLaw Z (multivariateGaussian 0 h.covMat) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω))
      Filter.atTop Z (fun _ => P) P' := by
  refine HansenEconometrics.cramerWold_tendstoInDistribution ?_ hZ.aemeasurable ?_
  · -- The normalized vector partial sums are a.e.-measurable, coordinate by coordinate.
    intro n
    refine (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).measurable.comp_aemeasurable ?_
    refine aemeasurable_pi_iff.2 fun i => ?_
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact (Finset.aemeasurable_fun_sum _ fun (s : ℕ) _ =>
      h.aemeasurable_apply ((s : ℤ) + 1) i).const_mul _
  · -- Each fixed inner-product projection converges to the matching Gaussian projection.
    intro t
    let a : k → ℝ := t.ofLp
    -- The projection of `multivariateGaussian 0 Σ` along `t` is `N(0, Var[a ⬝ u₁])`.
    have hgp : HasLaw
        (fun z : EuclideanSpace ℝ k => (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ k) t) z)
        (gaussianReal 0 (variance (fun ω => u 1 ω ⬝ᵥ a) P).toNNReal)
        (multivariateGaussian 0 h.covMat) := by
      rw [h.variance_proj a]
      refine (HansenEconometrics.hasLaw_multivariateGaussian_zero_dotProduct
        h.posSemidef a).congr (ae_of_all _ fun z => ?_)
      change inner ℝ t z = z.ofLp ⬝ᵥ a
      simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k) t.ofLp z.ofLp)
    -- The scalar CLT for the projected process, with reference the projection of `Z`.
    have hscalar := (h.proj a).central_limit (hgp.fun_comp hZ)
    refine TendstoInDistribution.congr (fun n => ?_) Filter.EventuallyEq.rfl hscalar
    refine ae_of_all P fun ω => ?_
    -- The projection of the normalized vector sum is the scalar normalized projected sum.
    have hV : inner ℝ t
          (WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ • ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω))
        = ((Real.sqrt (n : ℝ))⁻¹ • ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω) ⬝ᵥ a := by
      have hinner := EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k) a
        ((Real.sqrt (n : ℝ))⁻¹ • ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω)
      rw [star_trivial] at hinner
      exact hinner
    change (Real.sqrt (n : ℝ))⁻¹ * ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω ⬝ᵥ a
      = inner ℝ t
          (WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ • ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω))
    rw [hV, smul_dotProduct, smul_eq_mul, sum_dotProduct]

end MDSCentralLimitVec

/-!
## Hansen Theorem 14.15 — the central limit theorem for α-mixing processes (Gordin route)

This section develops the Gordin apparatus behind Hansen's Theorem 14.15 (a CLT for strictly
stationary α-mixing processes with `∑ α(ℓ)^{1−2/r} < ∞` and `E|u|^r < ∞` for some `r > 2`) and
lands the theorem in the same *bundle-conditional* form as the martingale-difference CLT 14.11.

The two Gordin pieces that close unconditionally from the Theorem 14.13 covariance inequalities
(`HansenEconometrics.Chapter14Mixing`) are proved in full:

* `summable_autocov_of_mixing` — **absolute summability of the autocovariances**, the fact that
  makes the long-run variance `Ω = ∑_{ℓ∈ℤ} γ(ℓ)` well defined. Each autocovariance obeys the
  Davydov bound `|γ(ℓ)| ≤ 8 ‖u₀‖_r² α(ℓ)^{1−2/r}` (Theorem 14.13.2, `r = q`), whence summability
  by comparison with the mixing hypothesis. The degenerate `α = 0` lags are handled honestly:
  there the past and future σ-algebras are genuinely independent
  (`indep_of_alphaDep_eq_zero`), so the covariance vanishes.
* `gordin_condExp_summable` — **`L¹`-summability of the conditional-expectation series**
  `∑_ℓ ∫ |E[uₗ | 𝓕₀]|`, the convergence that produces Gordin's `L¹` corrector process
  `Zₜ = ∑_ℓ E[u₍ₜ₊ₗ₎ | 𝓕₍ₜ₋₁₎]`. Each term obeys `∫ |E[uₗ | 𝓕₀]| ≤ 6 ‖u‖_r α(ℓ)^{1−1/r}`
  (Theorem 14.13.3, centered), and `α^{1−1/r} ≤ α^{1−2/r}` for `α ≤ 1` gives summability against
  the same mixing hypothesis.

The final endpoint `MixingCLTConditions.central_limit` is bundle-conditional in exactly the
Theorem 14.11 pattern: the structure `MixingCLTConditions` carries Hansen's genuine hypotheses
(strict stationarity, mean zero, `Lʳ`-integrability with `r > 2`, and the mixing summability)
together with one analytic field — pointwise convergence of the characteristic function of the
normalized partial sums to that of `N(0, Ω)` — which a full proof would derive by completing the
Gordin decomposition into a martingale-difference part plus an `L¹`-telescoping remainder and then
invoking the MDS CLT. See the honesty note on `gordin_condExp_summable` for the precise obstruction
to the remaining a.e.-telescoping step.
-/

section MixingCentralLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {u : ℤ → Ω → ℝ}

/-- The past σ-algebra of a measurable process is contained in the ambient σ-algebra. -/
private theorem pastSigma_le (hu : ∀ t, Measurable (u t)) (t : ℤ) :
    pastSigma u t ≤ mΩ :=
  iSup₂_le fun s _ => (hu s).comap_le

/-- The future σ-algebra of a measurable process is contained in the ambient σ-algebra. -/
private theorem futureSigma_le (hu : ∀ t, Measurable (u t)) (t : ℤ) :
    futureSigma u t ≤ mΩ :=
  iSup₂_le fun s _ => (hu s).comap_le

/-- Each coordinate `u t` is `pastSigma u t`-strongly-measurable (it is measurable with respect to
the σ-algebra it itself generates, which is contained in the past). -/
private theorem stronglyMeasurable_pastSigma_self (u : ℤ → Ω → ℝ) (t : ℤ) :
    StronglyMeasurable[pastSigma u t] (u t) :=
  ((comap_measurable (u t)).mono (comap_le_pastSigma u le_rfl) le_rfl).stronglyMeasurable

/-- Each coordinate `u t` is `futureSigma u t`-strongly-measurable. -/
private theorem stronglyMeasurable_futureSigma_self (u : ℤ → Ω → ℝ) (t : ℤ) :
    StronglyMeasurable[futureSigma u t] (u t) :=
  ((comap_measurable (u t)).mono (comap_le_futureSigma u le_rfl) le_rfl).stronglyMeasurable

/-- **Zero α-dependence is independence.** If the α-dependence coefficient of two σ-algebras
vanishes, then the σ-algebras are independent under `P`: every dependence discrepancy
`P(A ∩ B) − P(A)·P(B)` is squeezed to zero by the defining bound. This is the forward direction
complementing `alphaDep_eq_zero_of_indep`, used to discharge the degenerate `α = 0` lags in the
covariance summability argument. -/
private theorem indep_of_alphaDep_eq_zero {m₁ m₂ : MeasurableSpace Ω}
    (h : alphaDep m₁ m₂ P = 0) : Indep m₁ m₂ P := by
  rw [Indep_iff]
  intro A B hA hB
  have hdisc : |P.real (A ∩ B) - P.real A * P.real B| ≤ 0 := by
    rw [← h]; exact abs_measureReal_inter_sub_mul_le_alphaDep hA hB
  have heq : P.real (A ∩ B) = P.real A * P.real B :=
    sub_eq_zero.mp (abs_nonpos_iff.mp hdisc)
  have hfin1 : P (A ∩ B) ≠ ⊤ := measure_ne_top P _
  have hfin2 : P A * P B ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top P _) (measure_ne_top P _)
  rw [← ENNReal.toReal_eq_toReal_iff' hfin1 hfin2, ENNReal.toReal_mul]
  simpa only [measureReal_def] using heq

omit [IsProbabilityMeasure P] in
/-- **Single-coordinate stationarity.** From strict stationarity, `u ℓ` is identically distributed
to `u 0` under `P`, extracted from the singleton finite-dimensional law at shift `ℓ`. -/
private theorem identDistrib_stationary (hSS : IsStrictlyStationary u P) (ℓ : ℤ) :
    IdentDistrib (u ℓ) (u 0) P P := by
  have hmem : (0 : ℤ) ∈ ({0} : Finset ℤ) := Finset.mem_singleton.mpr rfl
  have hcomp := (hSS {0} ℓ).comp (u := fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩)
    (measurable_pi_apply _)
  have e1 : ((fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩) ∘
      fun ω => ({0} : Finset ℤ).restrict (fun t => u (t + ℓ) ω)) = u ℓ := by
    funext ω; change u (0 + ℓ) ω = u ℓ ω; rw [zero_add]
  have e2 : ((fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩) ∘
      fun ω => ({0} : Finset ℤ).restrict (fun t => u t ω)) = u 0 := by
    funext ω; rfl
  rw [e1, e2] at hcomp
  exact hcomp

/-- **Davydov autocovariance bound under mixing.** For a strictly stationary process `u` with each
coordinate measurable and `u₀ ∈ Lʳ` (`r > 2`), the lag-`ℓ` autocovariance is controlled by the
mixing coefficient: `|γ(ℓ)| ≤ 8 ‖u₀‖_r² · α(ℓ)^{1−2/r}` for every `ℓ : ℕ`. This is Hansen Theorem
14.13.2 applied with `X = u₀` past-measurable, `Z = u_ℓ` future-measurable, and `q = r`, followed
by `α(pastSigma u 0, futureSigma u ℓ) ≤ mixingCoeff u P ℓ`. The degenerate case
`α(pastSigma u 0, futureSigma u ℓ) = 0` is independence, so the covariance is exactly zero. -/
private theorem abs_autocov_le_mixing (hu : ∀ t, Measurable (u t))
    (hSS : IsStrictlyStationary u P) {r : ℝ} (hr : 2 < r)
    (hmem : MemLp (u 0) (ENNReal.ofReal r) P) (ℓ : ℕ) :
    |autocov u P (ℓ : ℤ)|
      ≤ 8 * (eLpNorm (u 0) (ENNReal.ofReal r) P).toReal ^ 2
          * mixingCoeff u P ℓ ^ (1 - 2 / r) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hexp_nonneg : (0 : ℝ) ≤ 1 - 2 / r := by
    rw [sub_nonneg]; exact (div_le_one hr0).mpr (by linarith)
  have hm₁ : pastSigma u 0 ≤ mΩ := pastSigma_le hu 0
  have hm₂ : futureSigma u (ℓ : ℤ) ≤ mΩ := futureSigma_le hu (ℓ : ℤ)
  have hX : StronglyMeasurable[pastSigma u 0] (u 0) := stronglyMeasurable_pastSigma_self u 0
  have hZ : StronglyMeasurable[futureSigma u (ℓ : ℤ)] (u (ℓ : ℤ)) :=
    stronglyMeasurable_futureSigma_self u (ℓ : ℤ)
  have hident : IdentDistrib (u (ℓ : ℤ)) (u 0) P P := identDistrib_stationary hSS (ℓ : ℤ)
  have hmemℓ : MemLp (u (ℓ : ℤ)) (ENNReal.ofReal r) P := hident.memLp_iff.mpr hmem
  have heLp : eLpNorm (u (ℓ : ℤ)) (ENNReal.ofReal r) P = eLpNorm (u 0) (ENNReal.ofReal r) P :=
    hident.eLpNorm_eq (ENNReal.ofReal r)
  have hle : alphaDep (pastSigma u 0) (futureSigma u (ℓ : ℤ)) P ≤ mixingCoeff u P ℓ := by
    have h := alphaDep_le_mixingCoeff (P := P) u ℓ (ℓ : ℤ)
    simpa using h
  have h2le : (2 : ENNReal) ≤ ENNReal.ofReal r := by
    have h := ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ r by linarith)
    simpa using h
  -- Reduce `autocov` to the covariance of `u 0` and `u ℓ`.
  rw [autocov, autocovAt, zero_add]
  rcases eq_or_lt_of_le (alphaDep_nonneg (pastSigma u 0) (futureSigma u (ℓ : ℤ)) P) with hα0 | hα
  · -- `α = 0`: the past and future σ-algebras are independent, so the covariance vanishes.
    have hIndep : Indep (pastSigma u 0) (futureSigma u (ℓ : ℤ)) P :=
      indep_of_alphaDep_eq_zero hα0.symm
    have hIF : (u 0) ⟂ᵢ[P] (u (ℓ : ℤ)) := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_right
        (indep_of_indep_of_le_left hIndep (comap_le_pastSigma u le_rfl))
        (comap_le_futureSigma u le_rfl)
    have hcov0 : covariance (u 0) (u (ℓ : ℤ)) P = 0 :=
      hIF.covariance_eq_zero (hmem.mono_exponent h2le) (hmemℓ.mono_exponent h2le)
    rw [hcov0, abs_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (mixingCoeff_nonneg u P ℓ) _)
  · -- `α > 0`: Davydov's covariance inequality with `q = r`.
    have hrq : 1 / r + 1 / r < 1 := by
      have h2 : (2 : ℝ) / r < 1 := (div_lt_one hr0).mpr hr
      calc 1 / r + 1 / r = 2 / r := by ring
        _ < 1 := h2
    have hbound := abs_covariance_le_alphaDep_of_memLp hm₁ hm₂ hα (by linarith : (1:ℝ) < r)
      (by linarith : (1:ℝ) < r) hrq hX hZ hmem hmemℓ
    calc |covariance (u 0) (u (ℓ : ℤ)) P|
        ≤ 8 * (eLpNorm (u 0) (ENNReal.ofReal r) P).toReal
            * (eLpNorm (u (ℓ : ℤ)) (ENNReal.ofReal r) P).toReal
            * alphaDep (pastSigma u 0) (futureSigma u (ℓ : ℤ)) P ^ (1 - r⁻¹ - r⁻¹) := hbound
      _ = 8 * (eLpNorm (u 0) (ENNReal.ofReal r) P).toReal ^ 2
            * alphaDep (pastSigma u 0) (futureSigma u (ℓ : ℤ)) P ^ (1 - 2 / r) := by
          rw [heLp, show (1 : ℝ) - r⁻¹ - r⁻¹ = 1 - 2 / r by rw [div_eq_mul_inv]; ring]; ring
      _ ≤ 8 * (eLpNorm (u 0) (ENNReal.ofReal r) P).toReal ^ 2
            * mixingCoeff u P ℓ ^ (1 - 2 / r) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow (alphaDep_nonneg _ _ _) hle hexp_nonneg

/-- **Gordin piece 1 — absolute summability of the autocovariances (Hansen Theorem 14.15).**
Under strict stationarity, coordinate measurability, `u₀ ∈ Lʳ` with `r > 2`, and the mixing
summability hypothesis `∑ α(ℓ)^{1−2/r} < ∞`, the autocovariance sequence is absolutely summable.
This is the convergence that makes the long-run variance `Ω = ∑_{ℓ∈ℤ} γ(ℓ)` (see
`longRunVariance`) well defined. The proof compares `|γ(ℓ)|` with `8 ‖u₀‖_r² · α(ℓ)^{1−2/r}` via
`abs_autocov_le_mixing` and invokes the mixing hypothesis. -/
theorem summable_autocov_of_mixing (hu : ∀ t, Measurable (u t))
    (hSS : IsStrictlyStationary u P) {r : ℝ} (hr : 2 < r)
    (hmem : MemLp (u 0) (ENNReal.ofReal r) P)
    (hmix : Summable (fun ℓ : ℕ => mixingCoeff u P ℓ ^ (1 - 2 / r))) :
    Summable (fun ℓ : ℕ => |autocov u P (ℓ : ℤ)|) := by
  set C : ℝ := 8 * (eLpNorm (u 0) (ENNReal.ofReal r) P).toReal ^ 2 with hC
  refine Summable.of_nonneg_of_le (fun ℓ => abs_nonneg _)
    (fun ℓ => abs_autocov_le_mixing hu hSS hr hmem ℓ) ?_
  exact hmix.mul_left C

/-- **Convergence of the long-run-variance series.** The one-sided autocovariance series
`ℓ ↦ γ(ℓ+1)` appearing in `longRunVariance` is summable under the hypotheses of
`summable_autocov_of_mixing`, so the `∑'` in `longRunVariance` is a genuine (not conditionally
defaulted) sum. This is `summable_autocov_of_mixing` transported through `summable_abs_iff` and the
`(· + 1)`-index shift. -/
theorem summable_autocov_succ_of_mixing (hu : ∀ t, Measurable (u t))
    (hSS : IsStrictlyStationary u P) {r : ℝ} (hr : 2 < r)
    (hmem : MemLp (u 0) (ENNReal.ofReal r) P)
    (hmix : Summable (fun ℓ : ℕ => mixingCoeff u P ℓ ^ (1 - 2 / r))) :
    Summable (fun ℓ : ℕ => autocov u P ((ℓ : ℤ) + 1)) := by
  have hsum : Summable (fun ℓ : ℕ => autocov u P (ℓ : ℤ)) :=
    summable_abs_iff.mp (summable_autocov_of_mixing hu hSS hr hmem hmix)
  refine ((summable_nat_add_iff 1).mpr hsum).congr (fun ℓ => ?_)
  congr 1

/-- **The long-run variance** `Ω = ∑_{ℓ∈ℤ} γ(ℓ) = γ(0) + 2 ∑_{ℓ≥1} γ(ℓ)` of a covariance-stationary
process (Hansen §14.15). Written in the one-sided form using the symmetry `γ(−ℓ) = γ(ℓ)`; its
`∑'` is genuinely convergent under the hypotheses of `summable_autocov_of_mixing` (see
`summable_autocov_succ_of_mixing`). This is the asymptotic variance of the normalized partial
sums `√n · ū`. -/
noncomputable def longRunVariance (u : ℤ → Ω → ℝ) (P : Measure Ω) : ℝ :=
  autocov u P 0 + 2 * ∑' ℓ : ℕ, autocov u P ((ℓ : ℤ) + 1)

/-- **Davydov conditional-expectation bound under mixing.** For a strictly stationary mean-zero
process with each coordinate measurable and `u₀ ∈ Lʳ` (`r > 2`), the `L¹` norm of the conditional
expectation of `u_ℓ` given the past `𝓕₀` obeys `∫ |E[u_ℓ | 𝓕₀]| ≤ 6 ‖u₀‖_r · α(ℓ)^{1−2/r}`. This is
Hansen Theorem 14.13.3 (centered), applied with `Z = u_ℓ` future-measurable and conditioning
σ-algebra `𝓕₀ = pastSigma u 0`, followed by `α^{1−1/r} ≤ α^{1−2/r}` (for `α ≤ 1`) and
`α ≤ mixingCoeff u P ℓ`. The degenerate `α = 0` lag is independence, where the conditional
expectation collapses to the (zero) mean by `condExp_indep_eq`. -/
private theorem integral_abs_condExp_le_mixing (hu : ∀ t, Measurable (u t))
    (hSS : IsStrictlyStationary u P) {r : ℝ} (hr : 2 < r)
    (hmem : MemLp (u 0) (ENNReal.ofReal r) P) (hmean : P[u 0] = 0) (ℓ : ℕ) :
    ∫ ω, |(P[u (ℓ : ℤ) | pastSigma u 0]) ω| ∂P
      ≤ 6 * (eLpNorm (u 0) (ENNReal.ofReal r) P).toReal * mixingCoeff u P ℓ ^ (1 - 2 / r) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hrinv_le : r⁻¹ ≤ 1 := by rw [inv_le_one₀ hr0]; linarith
  have hm₁ : pastSigma u 0 ≤ mΩ := pastSigma_le hu 0
  have hm₂ : futureSigma u (ℓ : ℤ) ≤ mΩ := futureSigma_le hu (ℓ : ℤ)
  have hZ : StronglyMeasurable[futureSigma u (ℓ : ℤ)] (u (ℓ : ℤ)) :=
    stronglyMeasurable_futureSigma_self u (ℓ : ℤ)
  have hident : IdentDistrib (u (ℓ : ℤ)) (u 0) P P := identDistrib_stationary hSS (ℓ : ℤ)
  have hmemℓ : MemLp (u (ℓ : ℤ)) (ENNReal.ofReal r) P := hident.memLp_iff.mpr hmem
  have heLp : eLpNorm (u (ℓ : ℤ)) (ENNReal.ofReal r) P = eLpNorm (u 0) (ENNReal.ofReal r) P :=
    hident.eLpNorm_eq (ENNReal.ofReal r)
  have hmeanℓ : P[u (ℓ : ℤ)] = 0 := by rw [hident.integral_eq, hmean]
  have hnonnegRHS : (0 : ℝ) ≤ 6 * (eLpNorm (u 0) (ENNReal.ofReal r) P).toReal
      * mixingCoeff u P ℓ ^ (1 - 2 / r) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (mixingCoeff_nonneg u P ℓ) _)
  rcases eq_or_lt_of_le (alphaDep_nonneg (pastSigma u 0) (futureSigma u (ℓ : ℤ)) P) with hα0 | hα
  · -- `α = 0`: independence collapses `E[u_ℓ | 𝓕₀]` to the mean `E[u_ℓ] = 0`.
    have hIndep : Indep (futureSigma u (ℓ : ℤ)) (pastSigma u 0) P :=
      (indep_of_alphaDep_eq_zero hα0.symm).symm
    have hce : P[u (ℓ : ℤ) | pastSigma u 0] =ᵐ[P] (fun _ => P[u (ℓ : ℤ)]) :=
      condExp_indep_eq hm₂ hm₁ hZ hIndep
    have hzeroae : (fun ω => |(P[u (ℓ : ℤ) | pastSigma u 0]) ω|) =ᵐ[P] (fun _ => (0 : ℝ)) := by
      filter_upwards [hce] with ω hω; simp only [hω, hmeanℓ, abs_zero]
    rw [integral_congr_ae hzeroae, integral_zero]
    exact hnonnegRHS
  · -- `α > 0`: Davydov's centered conditional-expectation inequality.
    have hle : alphaDep (pastSigma u 0) (futureSigma u (ℓ : ℤ)) P ≤ mixingCoeff u P ℓ := by
      have h := alphaDep_le_mixingCoeff (P := P) u ℓ (ℓ : ℤ); simpa using h
    have hmcpos : 0 < mixingCoeff u P ℓ := lt_of_lt_of_le hα hle
    have hmcle1 : mixingCoeff u P ℓ ≤ 1 := mixingCoeff_le_one (P := P) u ℓ
    have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
      have h := ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ r by linarith); simpa using h
    have hbound := integral_abs_condExp_le_eLpNorm hm₁ hm₂ hp1 ENNReal.ofReal_ne_top hα hZ hmemℓ
      hmeanℓ
    rw [ENNReal.toReal_ofReal hr0.le, heLp] at hbound
    refine hbound.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc alphaDep (pastSigma u 0) (futureSigma u (ℓ : ℤ)) P ^ (1 - r⁻¹)
        ≤ mixingCoeff u P ℓ ^ (1 - r⁻¹) :=
          Real.rpow_le_rpow (alphaDep_nonneg _ _ _) hle (by rw [sub_nonneg]; linarith)
      _ ≤ mixingCoeff u P ℓ ^ (1 - 2 / r) :=
          Real.rpow_le_rpow_of_exponent_ge hmcpos hmcle1
            (by rw [div_eq_mul_inv]; nlinarith [inv_nonneg.mpr hr0.le])

/-- **Gordin piece 2 — `L¹`-summability of the conditional-expectation series (Hansen Theorem
14.15).** Under strict stationarity, mean zero, coordinate measurability, `u₀ ∈ Lʳ` with `r > 2`,
and the mixing summability hypothesis, the series `∑_ℓ ∫ |E[u_ℓ | 𝓕₀]|` converges. This is the
`L¹` convergence that produces Gordin's corrector process `Zₜ = ∑_ℓ E[u₍ₜ₊ₗ₎ | 𝓕₍ₜ₋₁₎]`: absolute
convergence of these conditional expectations is exactly what lets one write `uₜ` as a
martingale-difference part plus an `L¹`-telescoping remainder `Zₜ − Z₍ₜ₊₁₎`.

**Honesty note (obstruction to the full decomposition).** This lemma lands the summability that the
Gordin construction rests on. The remaining step — assembling the a.e. identity
`uₜ = eₜ + Zₜ − Z₍ₜ₊₁₎` with `e` a genuine martingale difference sequence and verifying
`Var[e₁] = Ω` — is not carried out here: it requires constructing the `L¹`-limit process `Z` as an
honest random variable (an `L¹`-completeness/`tsum`-in-`Lᵖ` argument), the a.e. telescoping identity
(a Lévy upward/downward convergence argument for `condExp`), and the
Kolmogorov/uniform-integrability identification of `Var[e₁]` with the long-run variance. Those are
research-grade and are deferred; the endpoint below is therefore taken in the bundle-conditional
form matching Theorem 14.11, with the completed Gordin decomposition standing behind the single
analytic field. -/
theorem gordin_condExp_summable (hu : ∀ t, Measurable (u t))
    (hSS : IsStrictlyStationary u P) {r : ℝ} (hr : 2 < r)
    (hmem : MemLp (u 0) (ENNReal.ofReal r) P) (hmean : P[u 0] = 0)
    (hmix : Summable (fun ℓ : ℕ => mixingCoeff u P ℓ ^ (1 - 2 / r))) :
    Summable (fun ℓ : ℕ => ∫ ω, |(P[u (ℓ : ℤ) | pastSigma u 0]) ω| ∂P) := by
  refine Summable.of_nonneg_of_le (fun ℓ => integral_nonneg (fun ω => abs_nonneg _))
    (fun ℓ => integral_abs_condExp_le_mixing hu hSS hr hmem hmean ℓ) ?_
  exact hmix.mul_left (6 * (eLpNorm (u 0) (ENNReal.ofReal r) P).toReal)

/-!
### The Theorem 14.15 endpoint (bundle-conditional)
-/

/-- **Hansen Theorem 14.15 hypotheses (assumption bundle).**

The hypotheses of Hansen's central limit theorem for α-mixing processes, packaged in the
repository's bundle pattern (mirroring `MDSCLTConditions`). The genuine Hansen hypotheses are:

* `hr`, `stationary`, `measurable`, `mean_zero`, `memLp` — the process `u` is strictly stationary,
  measurable, mean zero, and `Lʳ`-integrable for some `r > 2`;
* `summable_mixing` — the strong-mixing coefficients satisfy `∑ α(ℓ)^{1−2/r} < ∞`;
* `nonneg` — the long-run variance `Ω = ∑_{ℓ∈ℤ} γ(ℓ)` is nonnegative (it is a limiting variance;
  this is the analogue of the positive-semidefiniteness field in the multivariate MDS bundle).

Under these hypotheses `summable_autocov_of_mixing` makes `Ω` well defined and
`gordin_condExp_summable` supplies the `L¹` convergence behind the Gordin decomposition. The final
field is the analytic core, carried exactly as in the martingale-difference bundle:

* `charFun_tendsto` — the characteristic function of the normalized partial sum
  `(√n)⁻¹ ∑_{t < n} u₍ₜ₊₁₎` converges pointwise to `s ↦ exp(−Ω·s²/2)`, the characteristic function
  of `N(0, Ω)`.

A full proof of Theorem 14.15 would derive `charFun_tendsto` from the other fields by completing the
Gordin decomposition (see the obstruction note on `gordin_condExp_summable`) and invoking the MDS
CLT `MDSCLTConditions.central_limit` on the martingale-difference part; the endpoint
`MixingCLTConditions.central_limit` then delivers the convergence-in-distribution conclusion. -/
structure MixingCLTConditions (u : ℤ → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- The `Lʳ` moment exponent, `r > 2`. -/
  r : ℝ
  /-- The moment exponent exceeds `2`. -/
  hr : 2 < r
  /-- The process is strictly stationary. -/
  stationary : IsStrictlyStationary u P
  /-- Each coordinate is measurable. -/
  measurable : ∀ t, Measurable (u t)
  /-- The process is mean zero. -/
  mean_zero : ∀ t, P[u t] = 0
  /-- The marginal `u₀` is `Lʳ`-integrable. -/
  memLp : MemLp (u 0) (ENNReal.ofReal r) P
  /-- The strong-mixing coefficients satisfy `∑ α(ℓ)^{1−2/r} < ∞`. -/
  summable_mixing : Summable (fun ℓ : ℕ => mixingCoeff u P ℓ ^ (1 - 2 / r))
  /-- The long-run variance is nonnegative (it is a limiting variance). -/
  nonneg : 0 ≤ longRunVariance u P
  /-- **The analytic core (bundle-conditional).** The characteristic function of the normalized
  partial sum `(√n)⁻¹ ∑_{t < n} u₍ₜ₊₁₎` converges pointwise to `s ↦ exp(−Ω·s²/2)`, the
  characteristic function of `N(0, Ω)` with `Ω = longRunVariance u P`. -/
  charFun_tendsto : ∀ s : ℝ,
    Filter.Tendsto
      (fun n : ℕ => charFun
        (P.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)) s)
      Filter.atTop (nhds (Complex.exp (-(longRunVariance u P : ℂ) * (s : ℂ) ^ 2 / 2)))

omit [IsProbabilityMeasure P] in
/-- The characteristic function of the Gaussian limit `N(0, Ω)` evaluated at `s` equals the analytic
target `exp(−Ω·s²/2)` of `MixingCLTConditions.charFun_tendsto`, using the bundle's nonnegativity of
`Ω` to discharge the `toNNReal` coercion `((Ω).toNNReal : ℝ) = Ω`. -/
private theorem charFun_gaussianReal_longRunVariance_eq (hnn : 0 ≤ longRunVariance u P) (s : ℝ) :
    charFun (gaussianReal 0 (longRunVariance u P).toNNReal) s
      = Complex.exp (-(longRunVariance u P : ℂ) * (s : ℂ) ^ 2 / 2) := by
  rw [charFun_gaussianReal]
  congr 1
  have hv : ((longRunVariance u P).toNNReal : ℝ) = longRunVariance u P := Real.coe_toNNReal _ hnn
  push_cast [hv]
  ring

/-- **Hansen Theorem 14.15 — central limit theorem for α-mixing processes (bundle endpoint).**

From the `MixingCLTConditions` bundle, the normalized partial sums `(√n)⁻¹ ∑_{t < n} u₍ₜ₊₁₎`
converge in distribution to a `N(0, Ω)` limit, `Ω = longRunVariance u P`, in the repository's
Chapter 7 convergence idiom: against any reference random variable `Z` with
`HasLaw Z (gaussianReal 0 Ω.toNNReal) P'`. The proof consumes the bundle's analytic field
`charFun_tendsto` through Mathlib's Lévy continuity theorem and identifies the limit with the
Gaussian via `charFun_gaussianReal_longRunVariance_eq`, exactly as
`MDSCLTConditions.central_limit` does for Theorem 14.11. -/
theorem MixingCLTConditions.central_limit {Ω' : Type*} {m' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → ℝ}
    (h : MixingCLTConditions u P)
    (hZ : HasLaw Z (gaussianReal 0 (longRunVariance u P).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)
      Filter.atTop Z (fun _ => P) P' where
  forall_aemeasurable n := by
    refine AEMeasurable.const_mul ?_ _
    exact Finset.aemeasurable_fun_sum _ fun i _ => (h.measurable ((i : ℤ) + 1)).aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun s => ?_
    rw! [hZ.map_eq]
    simpa [charFun_gaussianReal_longRunVariance_eq h.nonneg] using h.charFun_tendsto s

end MixingCentralLimit

end ProbabilityTheory
