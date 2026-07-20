import HansenEconometrics.Chapter14ARInversion
import HansenEconometrics.Chapter14LinearProcess
import HansenEconometrics.Chapter14Deterministic
import HansenEconometrics.ErgodicTheory.PathShift
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Fintype.BigOperators

/-!
# Chapter 14: Time Series — the AR(p) and ARMA(p, q) processes (Hansen Theorems 14.23, 14.25)

This file formalizes Hansen's *Econometrics* **Theorem 14.23** (the AR(p) process): the stationary
solution of the autoregression `Yₜ = α₀ + α₁ Yₜ₋₁ + ⋯ + αₚ Yₜ₋ₚ + eₜ`, with all roots of the AR
polynomial outside the unit circle, is the MA(∞) filter `Yₜ = μ + ∑ⱼ bⱼ eₜ₋ⱼ` of the innovations,
and this filter is strictly stationary, ergodic, and satisfies the AR recursion a.s.

Following the honest AR(1) pattern of `HansenEconometrics.Chapter14LinearProcess` (Theorem 14.21),
the process is *defined* as its MA(∞) solution `arProcess` and then shown to satisfy the recursion.
The stochastic layer builds on the linear-process engine (`linearProcess_summable_ae`,
`IsStrictlyStationary.linearProcess`, `IsErgodicProcess.linearProcess`) and the path-space shift
bridge (`HansenEconometrics.ErgodicTheory.PathShift`, Hansen Theorems 14.4/14.5).

## The deterministic coefficient layer (namespace `HansenTimeSeries`)

The reciprocal roots `λ : Fin p → ℂ` (with `‖λᵢ‖ < 1`) parametrize the AR polynomial
`α(z) = ∏ᵢ (1 - λᵢ z)`; a real AR polynomial is the case where the roots are closed under complex
conjugation (a permutation `σ` with `λ (σ i) = conj (λ i)`), which makes all coefficients real.

* `arCoeffReal` — the real MA(∞) coefficients `bⱼ = Re(arInverseCoeff λ j)` (the `zʲ` coefficients
  of `α(z)⁻¹`, from `HansenEconometrics.Chapter14ARInversion`, Hansen Theorem 14.24).
* `arPolyCoeff` — the real AR coefficients `αₗ`, extracted from `α(z) = 1 - α₁ z - ⋯ - αₚ zᵖ`.
* `arCoeffReal_recurrence` — **the coefficient-level content of Theorem 14.23:**
  `b_{m+1} = ∑ᵢ αᵢ₊₁ b_{m-i}`, obtained by extracting the `z^{m+1}` coefficient of the power-series
  identity `b(z) · α(z) = 1` (Hansen 14.24) and pushing it through the realness of the coefficients.
* `one_sub_sum_arPolyCoeff_ne_zero` — `1 - ∑ αᵢ = α(1) = ∏ᵢ (1 - λᵢ) ≠ 0`, so the AR mean
  `μ = α₀ / (1 - ∑ αᵢ)` is well defined.
* `summable_arCoeffReal` — absolute summability of `bⱼ` (Hansen 14.24).

## Theorem 14.23 (namespace `ProbabilityTheory`)

* `arProcess` — the MA(∞) solution `Yₜ = μ + ∑ⱼ bⱼ eₜ₋ⱼ`.
* `arProcess_summable_ae` — a.s. convergence of the defining series.
* `arProcess_strictlyStationary` — strict stationarity of the solution.
* `arProcess_ergodic` — ergodicity (with `arProcess_ergodic_of_iid`, the i.i.d. corollary via Hansen
  Theorem 14.4). Per Hansen (14.38) the innovations are stationary ergodic white noise, not assumed
  i.i.d.; only stationarity, ergodicity, and integrability are used.
* `arProcess_recursion` — **the substantive content:** the MA(∞) solution satisfies the AR(p)
  recursion `Yₜ = α₀ + ∑ᵢ αᵢ Yₜ₋ᵢ + eₜ` a.s.

## AR(2) corollary (Hansen Theorem 14.22, ergodic half)

* `ar2Process_stationary_ergodic` — the `p = 2` instance on Hansen's stationarity triangle, wired to
  the deterministic root-region equivalence `HansenTimeSeries.ar2_roots_in_unit_disk_iff`
  (`HansenEconometrics.Chapter14Deterministic`, Theorem 14.22(a)).

## The ARMA(p, q) extension (Hansen Theorem 14.25, namespace `ProbabilityTheory`)

The ARMA(p, q) process `Yₜ = α₀ + ∑ᵢ αᵢ Yₜ₋ᵢ + uₜ` with finite moving-average innovation
`uₜ = ∑_{k=0}^{q} θₖ eₜ₋ₖ` is obtained by feeding the finite MA filter into the AR(p) engine above.

* `maProcess` — the finite MA(q) innovation `uₜ = ∑ₖ θₖ eₜ₋ₖ`. Hansen normalizes `θ₀ = 1`; the
  coefficient vector `θ : Fin (q+1) → ℝ` here is *unconstrained*, a faithful generalization since
  the normalization is irrelevant to stationarity and ergodicity (it only matters for
  identification, §14.27 onward). Being a finite-window functional of `e`, `maProcess` inherits
  strict stationarity (`maProcess_strictlyStationary`, via Theorem 14.2), ergodicity
  (`maProcess_ergodic`, via Theorem 14.5), integrability (`maProcess_integrable`), and
  coordinatewise measurability (`maProcess_aemeasurable`) from `e`.
* `armaProcess lam θ α₀ e := arProcess lam α₀ (maProcess θ e)` — the ARMA(p, q) solution as the
  AR(p) MA(∞) solution driven by the finite MA innovation. Its strict stationarity, ergodicity, a.s.
  convergence, and AR recursion `Yₜ = α₀ + ∑ᵢ αᵢ Yₜ₋ᵢ + uₜ` (`armaProcess_strictlyStationary`,
  `armaProcess_ergodic`/`armaProcess_ergodic_of_iid`, `armaProcess_summable_ae`,
  `armaProcess_recursion`) are thin wrappers applying the four AR(p) theorems to the innovation
  `maProcess θ e`.

Hansen's cross-reference "(14.38)" for the ARMA equation is a typo — the ARMA equation is
unnumbered in the text. The pure-`e` MA(∞) representation `Yₜ = μ + ∑ⱼ cⱼ eₜ₋ⱼ` with convolved
coefficients `cⱼ = ∑_{k ≤ min(j,q)} θₖ b_{j−k}` is not needed for Theorem 14.25 and is omitted.

## Theorem 14.26 (mixing of linear processes, Pham–Tran) — documented deferral

Hansen Theorem 14.26 (strong mixing of a linear process under the Lipschitz innovation-density
hypothesis 14.43) is an external-citation result (Pham–Tran 1985); the β-mixing / coupling
machinery it requires is absent from Mathlib v4.29, so no stub is provided. See
`HansenEconometrics.Chapter14Mixing` for the same deferral note on the mixing side.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace HansenTimeSeries

variable {p : ℕ}

/-- The AR polynomial `α(z) = ∏ᵢ (1 - λᵢ z)` as a genuine polynomial in `ℂ[X]`, with `λ i = rᵢ⁻¹`
the reciprocal roots. Its coercion to `ℂ⟦X⟧` is the factored polynomial appearing in
`arInverseCoeff_mul_arPoly`; keeping a `Polynomial` on hand supplies the degree bound and the
evaluation `α(1) = ∏ᵢ (1 - λᵢ)` that a raw power series does not. -/
noncomputable def arPolyPoly (lam : Fin p → ℂ) : Polynomial ℂ :=
  ∏ i, (1 - Polynomial.C (lam i) * Polynomial.X)

/-- The coercion of `arPolyPoly` to a formal power series is the factored AR polynomial appearing in
`arInverseCoeff_mul_arPoly`. -/
theorem coe_arPolyPoly (lam : Fin p → ℂ) :
    ((arPolyPoly lam : Polynomial ℂ) : PowerSeries ℂ)
      = ∏ i, (1 - PowerSeries.C (lam i) * PowerSeries.X) := by
  rw [arPolyPoly, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

/-- The real MA(∞) coefficient `bⱼ = Re(arInverseCoeff λ j)`. When the reciprocal roots are closed
under conjugation (a real AR polynomial), `arInverseCoeff λ j` is already real and this is just its
real value; see `arCoeffReal_ofReal`. -/
noncomputable def arCoeffReal (lam : Fin p → ℂ) (j : ℕ) : ℝ :=
  (arInverseCoeff lam j).re

/-- The real AR coefficient `αₗ` (for `l = 1, …, p`), extracted from the AR polynomial
`α(z) = 1 - α₁ z - ⋯ - αₚ zᵖ = ∏ᵢ (1 - λᵢ z)`: the `zˡ` coefficient of `α` is `-αₗ`, so
`αₗ = -Re(coeff l (arPolyPoly λ))`. -/
noncomputable def arPolyCoeff (lam : Fin p → ℂ) (l : ℕ) : ℝ :=
  -((arPolyPoly lam).coeff l).re

/-- The constant coefficient of the AR polynomial is `1`. -/
theorem arPolyPoly_coeff_zero (lam : Fin p → ℂ) : (arPolyPoly lam).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, arPolyPoly, Polynomial.eval_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  simp

/-- Each degree-one factor `1 - C λᵢ X` has `natDegree ≤ 1`. -/
private lemma natDegree_factor_le (lam : Fin p → ℂ) (i : Fin p) :
    (1 - Polynomial.C (lam i) * Polynomial.X).natDegree ≤ 1 := by
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  refine max_le (by simp) ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  simp [Polynomial.natDegree_C, Polynomial.natDegree_X]

/-- The AR polynomial `α(z) = ∏ᵢ (1 - λᵢ z)` has `natDegree ≤ p`. -/
theorem natDegree_arPolyPoly_le (lam : Fin p → ℂ) : (arPolyPoly lam).natDegree ≤ p := by
  rw [arPolyPoly]
  refine le_trans (Polynomial.natDegree_prod_le Finset.univ
    (fun i => 1 - Polynomial.C (lam i) * Polynomial.X)) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => natDegree_factor_le lam i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- Realness of the AR-polynomial coefficients. If the reciprocal roots are closed under complex
conjugation (encoded by a permutation `σ` with `lam (σ i) = conj (lam i)`), then every coefficient
`coeff l (arPolyPoly λ)` is fixed by conjugation, hence real. This is the case of an AR polynomial
with real coefficients. -/
theorem starRingEnd_arPolyPoly_coeff (lam : Fin p → ℂ) (σ : Equiv.Perm (Fin p))
    (hσ : ∀ i, lam (σ i) = starRingEnd ℂ (lam i)) (l : ℕ) :
    starRingEnd ℂ ((arPolyPoly lam).coeff l) = (arPolyPoly lam).coeff l := by
  have hmap : (arPolyPoly lam).map (starRingEnd ℂ) = arPolyPoly lam := by
    rw [arPolyPoly, Polynomial.map_prod]
    rw [Finset.prod_congr rfl (g := fun i => 1 - Polynomial.C (lam (σ i)) * Polynomial.X)
      (fun i _ => by
        rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_X, ← hσ i])]
    exact Equiv.prod_comp σ (fun i => 1 - Polynomial.C (lam i) * Polynomial.X)
  calc starRingEnd ℂ ((arPolyPoly lam).coeff l)
      = ((arPolyPoly lam).map (starRingEnd ℂ)).coeff l := (Polynomial.coeff_map _ _).symm
    _ = (arPolyPoly lam).coeff l := by rw [hmap]

/-- Under the conjugation-closure hypothesis, `coeff l (arPolyPoly λ)` equals the cast of its own
real part. -/
theorem arPolyPoly_coeff_ofReal (lam : Fin p → ℂ) (σ : Equiv.Perm (Fin p))
    (hσ : ∀ i, lam (σ i) = starRingEnd ℂ (lam i)) (l : ℕ) :
    (((arPolyPoly lam).coeff l).re : ℂ) = (arPolyPoly lam).coeff l :=
  Complex.conj_eq_iff_re.mp (starRingEnd_arPolyPoly_coeff lam σ hσ l)

/-- Under the conjugation-closure hypothesis, `arInverseCoeff λ j` equals the cast of `arCoeffReal`.
This is the realness of the MA(∞) coefficients of a real AR polynomial. -/
theorem arCoeffReal_ofReal (lam : Fin p → ℂ) (σ : Equiv.Perm (Fin p))
    (hσ : ∀ i, lam (σ i) = starRingEnd ℂ (lam i)) (j : ℕ) :
    ((arCoeffReal lam j : ℝ) : ℂ) = arInverseCoeff lam j :=
  Complex.conj_eq_iff_re.mp (starRingEnd_arInverseCoeff lam σ hσ j)

/-- **The MA(∞)/AR-coefficient recurrence at the level of `ℂ`.** Extracting the `z^{m+1}`
coefficient of the identity `b(z) · α(z) = 1` (Hansen 14.24) gives `b_{m+1} = ∑ᵢ αᵢ₊₁ b_{m-i}` with
the convention that `b` of a negative lag is `0` (encoded by the `if i+1 ≤ m+1` guard). Here the AR
coefficient `αₗ` is `-coeff l (arPolyPoly λ)`. This is the coefficient-level content of the AR
recursion. The proof expands the coerced AR polynomial as the finite sum `∑_{l ≤ p} (coeff l) zˡ`
(degree `≤ p`), so `coeff_{m+1}(b · zˡ)` is exactly the guarded shift `b_{m+1-l}`. -/
theorem arInverseCoeff_recurrence (lam : Fin p → ℂ) (m : ℕ) :
    arInverseCoeff lam (m + 1)
      = ∑ i : Fin p, (-(arPolyPoly lam).coeff ((i : ℕ) + 1))
          * (if (i : ℕ) + 1 ≤ m + 1 then arInverseCoeff lam (m + 1 - ((i : ℕ) + 1)) else 0) := by
  classical
  set b : PowerSeries ℂ := PowerSeries.mk fun j => arInverseCoeff lam j with hb
  -- Generating-series identity (Hansen 14.24), with the AR polynomial as a coerced `Polynomial`.
  have hid : b * (↑(arPolyPoly lam) : PowerSeries ℂ) = 1 := by
    rw [hb, coe_arPolyPoly]; exact arInverseCoeff_mul_arPoly lam
  -- Finite (degree `≤ p`) expansion of the coerced AR polynomial.
  have hexp : (↑(arPolyPoly lam) : PowerSeries ℂ)
      = ∑ l ∈ Finset.range (p + 1),
          PowerSeries.C ((arPolyPoly lam).coeff l) * PowerSeries.X ^ l := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply]
    conv_lhs => rw [Polynomial.as_sum_range' (arPolyPoly lam) (p + 1)
      (Nat.lt_succ_of_le (natDegree_arPolyPoly_le lam))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  -- Coefficient `m+1` of `b · α = 1` is `0` (as `m + 1 ≠ 0`).
  have hcoeff : PowerSeries.coeff (m + 1)
      (b * ∑ l ∈ Finset.range (p + 1),
        PowerSeries.C ((arPolyPoly lam).coeff l) * PowerSeries.X ^ l) = 0 := by
    rw [← hexp, hid, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m)]
  -- Evaluate that coefficient termwise: `coeff_{m+1}(b · C(aₗ) · zˡ) = aₗ · (guarded b_{m+1-l})`.
  rw [Finset.mul_sum, map_sum] at hcoeff
  have hterm : ∀ l ∈ Finset.range (p + 1),
      PowerSeries.coeff (m + 1)
          (b * (PowerSeries.C ((arPolyPoly lam).coeff l) * PowerSeries.X ^ l))
        = (arPolyPoly lam).coeff l
            * (if l ≤ m + 1 then arInverseCoeff lam (m + 1 - l) else 0) := by
    intro l _
    rw [show b * (PowerSeries.C ((arPolyPoly lam).coeff l) * PowerSeries.X ^ l)
          = PowerSeries.C ((arPolyPoly lam).coeff l) * (b * PowerSeries.X ^ l) by ring,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
    rw [hb]
    simp only [PowerSeries.coeff_mk]
  rw [Finset.sum_congr rfl hterm] at hcoeff
  -- Peel the `l = 0` term (constant coefficient `1`), leaving `∑_{k<p} … + b_{m+1} = 0`.
  rw [Finset.sum_range_succ' (fun l => (arPolyPoly lam).coeff l
      * (if l ≤ m + 1 then arInverseCoeff lam (m + 1 - l) else 0)) p] at hcoeff
  simp only [Nat.zero_le, if_true, arPolyPoly_coeff_zero, one_mul, Nat.sub_zero] at hcoeff
  -- Rewrite the goal's `Fin p` sum as a `range p` sum and match.
  rw [Fin.sum_univ_eq_sum_range (fun k => (-(arPolyPoly lam).coeff (k + 1))
      * (if k + 1 ≤ m + 1 then arInverseCoeff lam (m + 1 - (k + 1)) else 0)) p]
  simp only [neg_mul]
  rw [Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_right hcoeff

/-- **The real MA(∞)/AR-coefficient recurrence (Hansen 14.23, coefficient level).** For a real AR
polynomial (reciprocal roots closed under conjugation), the real MA coefficients satisfy
`b_{m+1} = ∑ᵢ αᵢ₊₁ b_{m-i}` (with `b` of a negative lag read as `0`). This is
`arInverseCoeff_recurrence` pushed through the realness of the coefficients. It is the identity that
turns the MA(∞) solution into a solution of the AR recursion. -/
theorem arCoeffReal_recurrence (lam : Fin p → ℂ) (σ : Equiv.Perm (Fin p))
    (hσ : ∀ i, lam (σ i) = starRingEnd ℂ (lam i)) (m : ℕ) :
    arCoeffReal lam (m + 1)
      = ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1)
          * (if (i : ℕ) + 1 ≤ m + 1 then arCoeffReal lam (m + 1 - ((i : ℕ) + 1)) else 0) := by
  apply Complex.ofReal_injective
  rw [arCoeffReal_ofReal lam σ hσ, arInverseCoeff_recurrence lam m, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_zero,
    arCoeffReal_ofReal lam σ hσ, arPolyCoeff, Complex.ofReal_neg,
    arPolyPoly_coeff_ofReal lam σ hσ]

/-- The constant MA coefficient is `1`: `b₀ = 1`, since `arInverseCoeff λ 0 = 1`. -/
theorem arCoeffReal_zero (lam : Fin p → ℂ) : arCoeffReal lam 0 = 1 := by
  rw [arCoeffReal, arInverseCoeff]
  simp [Finset.Nat.antidiagonalTuple_zero_right]

/-- The AR polynomial evaluated at `1` is `∏ᵢ (1 - λᵢ)`, which is nonzero when every `‖λᵢ‖ < 1`.
Consequently `1 - ∑ᵢ αᵢ₊₁ = α(1) ≠ 0`, so the AR mean `μ = α₀ / (1 - ∑ αᵢ)` is well defined. This is
the real content of the "roots outside the unit circle" hypothesis for the intercept. -/
theorem one_sub_sum_arPolyCoeff_ne_zero (lam : Fin p → ℂ) (σ : Equiv.Perm (Fin p))
    (hσ : ∀ i, lam (σ i) = starRingEnd ℂ (lam i)) (hlam : ∀ i, ‖lam i‖ < 1) :
    (1 : ℝ) - ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1) ≠ 0 := by
  -- Both `↑(1 - ∑ αᵢ₊₁)` and `∏ᵢ (1 - λᵢ) = α(1)` equal `1 + ∑ᵢ coeff (i+1)` in `ℂ`.
  have hL : ((1 - ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1) : ℝ) : ℂ)
      = 1 + ∑ i : Fin p, (arPolyPoly lam).coeff ((i : ℕ) + 1) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_sum,
      show (∑ i : Fin p, ((arPolyCoeff lam ((i : ℕ) + 1) : ℝ) : ℂ))
          = ∑ i : Fin p, -((arPolyPoly lam).coeff ((i : ℕ) + 1)) from
        Finset.sum_congr rfl fun i _ => by
          rw [arPolyCoeff, Complex.ofReal_neg, arPolyPoly_coeff_ofReal lam σ hσ],
      Finset.sum_neg_distrib]
    ring
  have heval : (arPolyPoly lam).eval 1 = ∏ i, (1 - lam i) := by
    rw [arPolyPoly, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun i _ => by simp
  have hR : (∏ i, (1 - lam i)) = 1 + ∑ i : Fin p, (arPolyPoly lam).coeff ((i : ℕ) + 1) := by
    rw [← heval, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_arPolyPoly_le lam)),
      show (∑ l ∈ Finset.range (p + 1), (arPolyPoly lam).coeff l * (1 : ℂ) ^ l)
          = ∑ l ∈ Finset.range (p + 1), (arPolyPoly lam).coeff l from
        Finset.sum_congr rfl fun l _ => by rw [one_pow, mul_one],
      Finset.sum_range_succ' (fun l => (arPolyPoly lam).coeff l) p, arPolyPoly_coeff_zero,
      Fin.sum_univ_eq_sum_range (fun k => (arPolyPoly lam).coeff (k + 1)) p]
    ring
  have hcast : ((1 - ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1) : ℝ) : ℂ) = ∏ i, (1 - lam i) := by
    rw [hL, hR]
  have hprod : (∏ i, (1 - lam i)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    refine sub_ne_zero.mpr fun h => ?_
    have := hlam i; rw [← h] at this; simp at this
  have : ((1 - ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1) : ℝ) : ℂ) ≠ 0 := by
    rw [hcast]; exact hprod
  exact_mod_cast this

/-- A common bound `Λ < 1` on all reciprocal-root norms (the finitely many `‖λᵢ‖ < 1` have a
maximum below `1`). Feeds the summability of `arCoeffReal` through `summable_arInverseCoeff`. -/
theorem exists_norm_bound_lt_one (lam : Fin p → ℂ) (hlam : ∀ i, ‖lam i‖ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ Λ < 1 ∧ ∀ i, ‖lam i‖ ≤ Λ := by
  rcases isEmpty_or_nonempty (Fin p) with hemp | hne
  · exact ⟨0, le_refl 0, one_pos, fun i => (hemp.elim i)⟩
  · have hnonempty : (Finset.univ : Finset (Fin p)).Nonempty := Finset.univ_nonempty
    refine ⟨Finset.univ.sup' hnonempty (fun i => ‖lam i‖), ?_, ?_,
      fun i => Finset.le_sup' (fun i => ‖lam i‖) (Finset.mem_univ i)⟩
    · obtain ⟨i₀, _⟩ := hnonempty
      exact le_trans (norm_nonneg _) (Finset.le_sup' (fun i => ‖lam i‖) (Finset.mem_univ i₀))
    · rw [Finset.sup'_lt_iff]
      exact fun i _ => hlam i

/-- **Absolute summability of the real MA(∞) coefficients (Hansen 14.23 / 14.24).** With all
reciprocal roots of norm `< 1`, the coefficients `bⱼ = arCoeffReal λ j` are absolutely summable,
since `|bⱼ| ≤ ‖arInverseCoeff λ j‖` and the latter is summable by `summable_arInverseCoeff`. -/
theorem summable_arCoeffReal (lam : Fin p → ℂ) (hlam : ∀ i, ‖lam i‖ < 1) :
    Summable (fun j : ℕ => |arCoeffReal lam j|) := by
  obtain ⟨Λ, hΛ0, hΛ1, hbound⟩ := exists_norm_bound_lt_one lam hlam
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_)
    (summable_arInverseCoeff hΛ0 hΛ1 hbound)
  exact RCLike.abs_re_le_norm (arInverseCoeff lam j)

end HansenTimeSeries

namespace ProbabilityTheory

open HansenTimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {p : ℕ}

/-- **The AR(p) process (Hansen §14.23, MA(∞) solution).** For reciprocal roots `lam : Fin p → ℂ`,
intercept `α₀`, and an innovation process `e`, the moving-average solution of the AR(p) recursion is
`Yₜ = μ + ∑ⱼ bⱼ eₜ₋ⱼ`, with mean `μ = α₀ / (1 - ∑ᵢ αᵢ)` and real MA coefficients
`bⱼ = arCoeffReal λ j`.
When the roots lie outside the unit circle (all `‖λᵢ‖ < 1`) and `e` is stationary ergodic white
noise, this is the stationary ergodic AR(p) solution (`arProcess_strictlyStationary`,
`arProcess_ergodic`, `arProcess_recursion`). -/
noncomputable def arProcess (lam : Fin p → ℂ) (α₀ : ℝ) (e : ℤ → Ω → ℝ) : ℤ → Ω → ℝ :=
  fun t ω => α₀ / (1 - ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1))
    + ∑' j : ℕ, arCoeffReal lam j * e (t - j) ω

omit [IsProbabilityMeasure P] in
/-- **Hansen Theorem 14.23 (a.s. convergence of the MA(∞) series).** For roots outside the unit
circle and integrable, strictly stationary innovations, the MA(∞) series defining `arProcess`
converges a.s. Specializes `linearProcess_summable_ae` to `a j = arCoeffReal λ j`. -/
theorem arProcess_summable_ae {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (hlam : ∀ i, ‖lam i‖ < 1)
    (he : IsStrictlyStationary e P) (he_meas : ∀ t, AEMeasurable (e t) P)
    (he_int : Integrable (e 0) P) (t : ℤ) :
    ∀ᵐ ω ∂P, Summable (fun j : ℕ => arCoeffReal lam j * e (t - j) ω) :=
  linearProcess_summable_ae he he_meas he_int (summable_arCoeffReal lam hlam) t

/-- **Hansen Theorem 14.23 (strict stationarity of the AR(p) solution).** The MA(∞) solution
`arProcess` of a strictly stationary innovation process is strictly stationary. Mirrors
`ar1Process_strictlyStationary`: `arProcess` is the shift-equivariant functional
`φ q = μ + ∑ⱼ bⱼ q(-j)` of the whole innovation path, so
`IsStrictlyStationary.comp_shiftEquivariant` (Hansen Theorem 14.2) applies. No root condition is
needed for stationarity (`tsum` is total). -/
theorem arProcess_strictlyStationary {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (α₀ : ℝ)
    (he : IsStrictlyStationary e P) (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsStrictlyStationary (arProcess lam α₀ e) P := by
  set φ : (ℤ → ℝ) → ℝ := fun q => α₀ / (1 - ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1))
    + ∑' j : ℕ, arCoeffReal lam j * q (-(j : ℤ)) with hφ
  have hφmeas : Measurable φ :=
    measurable_const.add
      (measurable_tsum_real fun j => measurable_const.mul (measurable_pi_apply _))
  have hkey : IsStrictlyStationary (fun t ω => φ (fun j => e (t + j) ω)) P :=
    IsStrictlyStationary.comp_shiftEquivariant hφmeas he he_meas
  have heq : (fun t ω => φ (fun j => e (t + j) ω)) = arProcess lam α₀ e := by
    funext t ω
    simp only [hφ, arProcess]
    exact congrArg _ (tsum_congr fun j => by rw [sub_eq_add_neg])
  rwa [heq] at hkey

omit [IsProbabilityMeasure P] in
/-- **Hansen Theorem 14.23 (ergodicity of the AR(p) solution).** The MA(∞) solution `arProcess` of a
strictly stationary *ergodic* innovation process is ergodic. Mirrors `arProcess_strictlyStationary`
with the ergodic keystone `IsErgodicProcess.comp_shiftEquivariant` (Hansen Theorem 14.5) in place of
the stationarity keystone. Following Hansen (14.38), `e` is stationary ergodic white noise, not
assumed i.i.d.; only ergodicity of `e` and coordinatewise measurability are used. -/
theorem arProcess_ergodic {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (α₀ : ℝ)
    (hee : IsErgodicProcess e P) (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsErgodicProcess (arProcess lam α₀ e) P := by
  set φ : (ℤ → ℝ) → ℝ := fun q => α₀ / (1 - ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1))
    + ∑' j : ℕ, arCoeffReal lam j * q (-(j : ℤ)) with hφ
  have hφmeas : Measurable φ :=
    measurable_const.add
      (measurable_tsum_real fun j => measurable_const.mul (measurable_pi_apply _))
  have hkey : IsErgodicProcess (fun t ω => φ (fun j => e (t + j) ω)) P :=
    hee.comp_shiftEquivariant hφmeas he_meas
  have heq : (fun t ω => φ (fun j => e (t + j) ω)) = arProcess lam α₀ e := by
    funext t ω
    simp only [hφ, arProcess]
    exact congrArg _ (tsum_congr fun j => by rw [sub_eq_add_neg])
  rwa [heq] at hkey

/-- **Hansen Theorem 14.23 (ergodicity, i.i.d. corollary).** If the innovations are i.i.d. (rather
than merely stationary ergodic white noise), the AR(p) solution is ergodic — the i.i.d. innovations
are ergodic by `IsErgodicProcess.of_iid` (Hansen Theorem 14.4). -/
theorem arProcess_ergodic_of_iid {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (α₀ : ℝ)
    (he_indep : iIndepFun e P) (he_ident : ∀ t s, IdentDistrib (e t) (e s) P P)
    (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsErgodicProcess (arProcess lam α₀ e) P :=
  arProcess_ergodic lam α₀ (IsErgodicProcess.of_iid he_indep he_ident he_meas) he_meas

omit [IsProbabilityMeasure P] in
/-- **Hansen Theorem 14.23 (the AR(p) recursion holds a.s.).** The MA(∞) solution `arProcess`
satisfies the AR(p) recursion `Yₜ = α₀ + ∑ᵢ αᵢ Yₜ₋ᵢ + eₜ` for almost every `ω`. This is the
substantive content: the process *defined* as the MA(∞) series is genuinely a solution of the AR
recursion. The proof substitutes the MA(∞) form, reindexes each `t-(i+1)` series to align on the
lag `m+1` (via `Summable.sum_add_tsum_nat_add`), interchanges the finite sum over roots with the
`tsum` (`Summable.tsum_finsetSum`), and collapses the resulting coefficient sum with the
coefficient recurrence `arCoeffReal_recurrence`; the intercept bookkeeping uses the fixed point
`α₀ + (∑ αᵢ) μ = μ` for the AR mean `μ = α₀ / (1 - ∑ αᵢ)`. Requires the root condition (all
`‖λᵢ‖ < 1`) both for the a.s. convergence and, through conjugation closure, for the coefficient
recurrence. -/
theorem arProcess_recursion {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (α₀ : ℝ)
    (hlam : ∀ i, ‖lam i‖ < 1) (σ : Equiv.Perm (Fin p))
    (hσ : ∀ i, lam (σ i) = starRingEnd ℂ (lam i))
    (he : IsStrictlyStationary e P) (he_meas : ∀ t, AEMeasurable (e t) P)
    (he_int : Integrable (e 0) P) (t : ℤ) :
    ∀ᵐ ω ∂P, arProcess lam α₀ e t ω
      = α₀ + ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1)
          * arProcess lam α₀ e (t - (((i : ℕ) : ℤ) + 1)) ω + e t ω := by
  classical
  set s : ℝ := ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1) with hs
  set μ : ℝ := α₀ / (1 - s) with hμ
  have hs_ne : (1 : ℝ) - s ≠ 0 := one_sub_sum_arPolyCoeff_ne_zero lam σ hσ hlam
  have hμfix : α₀ + s * μ = μ := by rw [hμ]; field_simp; ring
  have hSti : ∀ᵐ ω ∂P, ∀ i : Fin p,
      Summable (fun j : ℕ => arCoeffReal lam j * e (t - (((i : ℕ) : ℤ) + 1) - ↑j) ω) :=
    ae_all_iff.mpr fun i =>
      arProcess_summable_ae lam hlam he he_meas he_int (t - (((i : ℕ) : ℤ) + 1))
  have hSt := arProcess_summable_ae lam hlam he he_meas he_int t
  filter_upwards [hSt, hSti] with ω hSt_ω hSti_ω
  -- Aligned tail coefficient functions: `G i m` is the `m`-th term of the `i`-th shifted series.
  set G : Fin p → ℕ → ℝ := fun i m =>
    if (i : ℕ) + 1 ≤ m + 1 then
      arCoeffReal lam (m + 1 - ((i : ℕ) + 1)) * e (t - (↑(m + 1) : ℤ)) ω else 0 with hG
  -- Each `G i` is summable: `G i (· + i)` is the summable `t-(i+1)` MA(∞) series.
  have hGsum : ∀ i : Fin p, Summable (G i) := by
    intro i
    rw [← summable_nat_add_iff (i : ℕ)]
    refine (hSti_ω i).congr fun m => ?_
    have hguard : (i : ℕ) + 1 ≤ m + (i : ℕ) + 1 := by omega
    simp only [hG]
    rw [if_pos hguard]
    have hidx : m + (i : ℕ) + 1 - ((i : ℕ) + 1) = m := by omega
    rw [hidx]
    have hti : t - (((i : ℕ) : ℤ) + 1) - ↑m = t - (↑(m + (i : ℕ) + 1) : ℤ) := by push_cast; ring
    rw [hti]
  -- Reindex the `i`-th `t-(i+1)` series to the aligned `m+1` form.
  have hshift : ∀ i : Fin p,
      (∑' j : ℕ, arCoeffReal lam j * e (t - (((i : ℕ) : ℤ) + 1) - ↑j) ω) = ∑' m : ℕ, G i m := by
    intro i
    rw [← (hGsum i).sum_add_tsum_nat_add (i : ℕ)]
    have hz : (∑ k ∈ Finset.range (i : ℕ), G i k) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      simp only [Finset.mem_range] at hk
      simp only [hG, if_neg (show ¬ (i : ℕ) + 1 ≤ k + 1 by omega)]
    rw [hz, zero_add]
    refine tsum_congr fun m => ?_
    have hguard : (i : ℕ) + 1 ≤ m + (i : ℕ) + 1 := by omega
    simp only [hG]
    rw [if_pos hguard]
    have hidx : m + (i : ℕ) + 1 - ((i : ℕ) + 1) = m := by omega
    rw [hidx]
    have hti : t - (((i : ℕ) : ℤ) + 1) - ↑m = t - (↑(m + (i : ℕ) + 1) : ℤ) := by push_cast; ring
    rw [hti]
  -- (A) Peel the `j = 0` term of the `t` series (`b₀ = 1`).
  have hA : (∑' j : ℕ, arCoeffReal lam j * e (t - ↑j) ω)
      = e t ω + ∑' m : ℕ, arCoeffReal lam (m + 1) * e (t - (↑(m + 1) : ℤ)) ω := by
    rw [hSt_ω.tsum_eq_zero_add]
    congr 1
    rw [arCoeffReal_zero]
    simp
  -- (C) Key convolution identity: the finite-sum-of-tsums collapses via the recurrence.
  have hC : (∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1)
        * ∑' j : ℕ, arCoeffReal lam j * e (t - (((i : ℕ) : ℤ) + 1) - ↑j) ω)
      = ∑' m : ℕ, arCoeffReal lam (m + 1) * e (t - (↑(m + 1) : ℤ)) ω := by
    have hstep : ∀ i : Fin p,
        arPolyCoeff lam ((i : ℕ) + 1)
            * ∑' j : ℕ, arCoeffReal lam j * e (t - (((i : ℕ) : ℤ) + 1) - ↑j) ω
          = ∑' m : ℕ, arPolyCoeff lam ((i : ℕ) + 1) * G i m :=
      fun i => by rw [hshift i, tsum_mul_left]
    rw [Finset.sum_congr rfl fun i _ => hstep i]
    have hswap := Summable.tsum_finsetSum (s := (Finset.univ : Finset (Fin p)))
      (f := fun (i : Fin p) m => arPolyCoeff lam ((i : ℕ) + 1) * G i m)
      (fun i _ => (hGsum i).mul_left _)
    rw [← hswap]
    refine tsum_congr fun m => ?_
    have hfactor : (∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1) * G i m)
        = (∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1)
            * (if (i : ℕ) + 1 ≤ m + 1 then arCoeffReal lam (m + 1 - ((i : ℕ) + 1)) else 0))
          * e (t - (↑(m + 1) : ℤ)) ω := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hG]
      split_ifs with h <;> ring
    rw [hfactor, ← arCoeffReal_recurrence lam σ hσ m]
  -- Assemble: substitute the MA(∞) form and reduce with (A), (C), and the fixed point.
  simp only [arProcess, ← hs, ← hμ]
  have hRHS : (∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1)
        * (μ + ∑' j : ℕ, arCoeffReal lam j * e (t - (((i : ℕ) : ℤ) + 1) - ↑j) ω))
      = s * μ + ∑' m : ℕ, arCoeffReal lam (m + 1) * e (t - (↑(m + 1) : ℤ)) ω := by
    rw [Finset.sum_congr rfl fun i _ => mul_add _ _ _, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← hs, hC]
  rw [hA, hRHS]
  linear_combination -hμfix

/-- **Hansen Theorem 14.22 (ergodic half): the AR(2) process on the stationarity triangle.** For
real AR(2) coefficients `(α₁, α₂)` in Hansen's stationarity triangle
`α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ -1 < α₂` (equations 14.35–14.37), let `z₁, z₂` be the roots of the
companion characteristic polynomial `z² - α₁ z - α₂` (equivalently the reciprocal roots of the AR
polynomial), so they satisfy the Vieta relations `z₁ + z₂ = α₁`, `z₁ z₂ = -α₂`. The triangle
conditions are equivalent to both roots lying in the open unit disk
(`HansenTimeSeries.ar2_roots_in_unit_disk_iff`, Hansen Theorem 14.22(a)), so the AR(2) MA(∞)
solution `arProcess ![z₁, z₂] α₀ e` of i.i.d. integrable innovations is strictly stationary and
ergodic, and
its defining MA(∞) series converges a.s. This is the `p = 2` instance of the AR(p) results
`arProcess_strictlyStationary` / `arProcess_ergodic_of_iid` / `arProcess_summable_ae`; the AR(2)
recursion itself is the `p = 2` case of `arProcess_recursion` (the reciprocal roots of a real AR(2)
polynomial are conjugation-closed, supplying its `σ` hypothesis). -/
theorem ar2Process_stationary_ergodic {e : ℤ → Ω → ℝ} (α₀ α₁ α₂ : ℝ) (z₁ z₂ : ℂ)
    (hsum : z₁ + z₂ = (α₁ : ℂ)) (hprod : z₁ * z₂ = ((-α₂ : ℝ) : ℂ))
    (htri : α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ -1 < α₂)
    (he_indep : iIndepFun e P) (he_ident : ∀ t s, IdentDistrib (e t) (e s) P P)
    (he_meas : ∀ t, AEMeasurable (e t) P) (he_int : Integrable (e 0) P) :
    IsStrictlyStationary (arProcess ![z₁, z₂] α₀ e) P ∧
      IsErgodicProcess (arProcess ![z₁, z₂] α₀ e) P ∧
      ∀ t : ℤ, ∀ᵐ ω ∂P, Summable (fun j : ℕ => arCoeffReal ![z₁, z₂] j * e (t - j) ω) := by
  have hdisk : ‖z₁‖ < 1 ∧ ‖z₂‖ < 1 :=
    (ar2_roots_in_unit_disk_iff α₁ α₂ z₁ z₂ hsum hprod).mpr htri
  have hlam : ∀ i, ‖(![z₁, z₂] : Fin 2 → ℂ) i‖ < 1 := by
    intro i
    fin_cases i
    · simpa using hdisk.1
    · simpa using hdisk.2
  have he_stat : IsStrictlyStationary e P := IsStrictlyStationary.of_iid he_indep he_ident he_meas
  exact ⟨arProcess_strictlyStationary _ α₀ he_stat he_meas,
    arProcess_ergodic_of_iid _ α₀ he_indep he_ident he_meas,
    fun t => arProcess_summable_ae _ hlam he_stat he_meas he_int t⟩

variable {q : ℕ}

/-- **The finite MA(q) innovation filter (Hansen §14.25).** For MA coefficients `θ : Fin (q+1) → ℝ`
and a base process `e`, the moving-average filter `uₜ = ∑_{k=0}^{q} θₖ eₜ₋ₖ`. Hansen normalizes
`θ₀ = 1`; the vector `θ` here is unconstrained (the normalization is irrelevant to stationarity and
ergodicity, mattering only for identification). This is the innovation fed into the AR(p) engine to
form `armaProcess` (Hansen Theorem 14.25). -/
noncomputable def maProcess (θ : Fin (q + 1) → ℝ) (e : ℤ → Ω → ℝ) : ℤ → Ω → ℝ :=
  fun t ω => ∑ k : Fin (q + 1), θ k * e (t - ((k : ℕ) : ℤ)) ω

/-- **Strict stationarity of the finite MA innovation (Hansen §14.25, via Theorem 14.2).** The
finite MA filter `maProcess θ e` is the shift-equivariant finite-window functional
`φ y = ∑ₖ θₖ · y(−k)` of the innovation path, so `IsStrictlyStationary.comp_shiftEquivariant`
(Hansen Theorem 14.2) transports strict stationarity from `e`. The functional is a finite sum of
coordinate evaluations, so no `tsum` and no summability hypothesis are needed. -/
theorem maProcess_strictlyStationary (θ : Fin (q + 1) → ℝ) {e : ℤ → Ω → ℝ}
    (he : IsStrictlyStationary e P) (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsStrictlyStationary (maProcess θ e) P := by
  set φ : (ℤ → ℝ) → ℝ := fun y => ∑ k : Fin (q + 1), θ k * y (-((k : ℕ) : ℤ)) with hφ
  have hφmeas : Measurable φ :=
    Finset.measurable_fun_sum _ fun k _ => measurable_const.mul (measurable_pi_apply _)
  have hkey : IsStrictlyStationary (fun t ω => φ (fun j => e (t + j) ω)) P :=
    IsStrictlyStationary.comp_shiftEquivariant hφmeas he he_meas
  have heq : (fun t ω => φ (fun j => e (t + j) ω)) = maProcess θ e := by
    funext t ω
    simp only [hφ, maProcess]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_eq_add_neg]
  rwa [heq] at hkey

omit [IsProbabilityMeasure P] in
/-- **Ergodicity of the finite MA innovation (Hansen §14.25, via Theorem 14.5).** Mirrors
`maProcess_strictlyStationary` with the ergodic keystone `IsErgodicProcess.comp_shiftEquivariant`
(Hansen Theorem 14.5) in place of the stationarity keystone. Only ergodicity of `e` and
coordinatewise measurability are used. -/
theorem maProcess_ergodic (θ : Fin (q + 1) → ℝ) {e : ℤ → Ω → ℝ}
    (hee : IsErgodicProcess e P) (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsErgodicProcess (maProcess θ e) P := by
  set φ : (ℤ → ℝ) → ℝ := fun y => ∑ k : Fin (q + 1), θ k * y (-((k : ℕ) : ℤ)) with hφ
  have hφmeas : Measurable φ :=
    Finset.measurable_fun_sum _ fun k _ => measurable_const.mul (measurable_pi_apply _)
  have hkey : IsErgodicProcess (fun t ω => φ (fun j => e (t + j) ω)) P :=
    hee.comp_shiftEquivariant hφmeas he_meas
  have heq : (fun t ω => φ (fun j => e (t + j) ω)) = maProcess θ e := by
    funext t ω
    simp only [hφ, maProcess]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_eq_add_neg]
  rwa [heq] at hkey

omit [IsProbabilityMeasure P] in
/-- **Coordinatewise measurability of the finite MA innovation.** A finite sum of the AE-measurable
coordinate processes `ω ↦ θₖ · e (t − k) ω`. -/
theorem maProcess_aemeasurable (θ : Fin (q + 1) → ℝ) {e : ℤ → Ω → ℝ}
    (he_meas : ∀ t, AEMeasurable (e t) P) (t : ℤ) :
    AEMeasurable (maProcess θ e t) P := by
  change AEMeasurable (fun ω => ∑ k : Fin (q + 1), θ k * e (t - ((k : ℕ) : ℤ)) ω) P
  exact Finset.aemeasurable_fun_sum _ fun k _ => (he_meas _).const_mul (θ k)

omit [IsProbabilityMeasure P] in
/-- **Integrability of the finite MA innovation at time 0.** A finite sum of the integrable
processes `ω ↦ θₖ · e (−k) ω`; strict stationarity transports `Integrable (e 0)` to each lag via
`identDistrib_of_strictlyStationary`. This supplies the `Integrable (·₀)` hypothesis of the AR(p)
theorems when the innovation is `maProcess θ e`. -/
theorem maProcess_integrable (θ : Fin (q + 1) → ℝ) {e : ℤ → Ω → ℝ}
    (he : IsStrictlyStationary e P) (he_int : Integrable (e 0) P) :
    Integrable (maProcess θ e 0) P := by
  change Integrable (fun ω => ∑ k : Fin (q + 1), θ k * e (0 - ((k : ℕ) : ℤ)) ω) P
  refine integrable_finset_sum _ fun k _ => ?_
  exact ((identDistrib_of_strictlyStationary he (0 - ((k : ℕ) : ℤ))).integrable_iff.mpr
    he_int).const_mul (θ k)

/-- **The ARMA(p, q) process (Hansen Theorem 14.25).** For reciprocal roots `lam : Fin p → ℂ`, MA
coefficients `θ : Fin (q+1) → ℝ`, intercept `α₀`, and innovation `e`, the ARMA(p, q) solution is the
AR(p) MA(∞) solution driven by the finite MA innovation `uₜ = ∑ₖ θₖ eₜ₋ₖ`:
`armaProcess lam θ α₀ e := arProcess lam α₀ (maProcess θ e)`. Under roots outside the unit circle
(all `‖λᵢ‖ < 1`) and stationary ergodic white-noise `e`, it is strictly stationary, ergodic, a.s.
convergent, and satisfies the ARMA recursion (`armaProcess_strictlyStationary`,
`armaProcess_ergodic`, `armaProcess_summable_ae`, `armaProcess_recursion`). -/
noncomputable def armaProcess (lam : Fin p → ℂ) (θ : Fin (q + 1) → ℝ) (α₀ : ℝ) (e : ℤ → Ω → ℝ) :
    ℤ → Ω → ℝ :=
  arProcess lam α₀ (maProcess θ e)

/-- **Hansen Theorem 14.25 (a.s. convergence of the MA(∞) series).** The MA(∞) series defining
`armaProcess` converges a.s. This is `arProcess_summable_ae` applied to the finite MA innovation
`maProcess θ e`, whose stationarity, measurability, and integrability come from the `maProcess_*`
lemmas. -/
theorem armaProcess_summable_ae {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (θ : Fin (q + 1) → ℝ)
    (hlam : ∀ i, ‖lam i‖ < 1) (he : IsStrictlyStationary e P)
    (he_meas : ∀ t, AEMeasurable (e t) P) (he_int : Integrable (e 0) P) (t : ℤ) :
    ∀ᵐ ω ∂P, Summable (fun j : ℕ => arCoeffReal lam j * maProcess θ e (t - j) ω) :=
  arProcess_summable_ae lam hlam (maProcess_strictlyStationary θ he he_meas)
    (maProcess_aemeasurable θ he_meas) (maProcess_integrable θ he he_int) t

/-- **Hansen Theorem 14.25 (strict stationarity of the ARMA solution).** The ARMA(p, q) process is
strictly stationary. This is `arProcess_strictlyStationary` applied to the finite MA innovation,
which is itself strictly stationary by `maProcess_strictlyStationary`. -/
theorem armaProcess_strictlyStationary {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (θ : Fin (q + 1) → ℝ)
    (α₀ : ℝ) (he : IsStrictlyStationary e P) (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsStrictlyStationary (armaProcess lam θ α₀ e) P :=
  arProcess_strictlyStationary lam α₀ (maProcess_strictlyStationary θ he he_meas)
    (maProcess_aemeasurable θ he_meas)

omit [IsProbabilityMeasure P] in
/-- **Hansen Theorem 14.25 (ergodicity of the ARMA solution).** The ARMA(p, q) process is ergodic.
This is `arProcess_ergodic` applied to the finite MA innovation, which is ergodic by
`maProcess_ergodic`. Following Hansen, `e` is stationary ergodic white noise, not assumed i.i.d.;
only ergodicity and coordinatewise measurability of `e` are used. -/
theorem armaProcess_ergodic {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (θ : Fin (q + 1) → ℝ) (α₀ : ℝ)
    (hee : IsErgodicProcess e P) (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsErgodicProcess (armaProcess lam θ α₀ e) P :=
  arProcess_ergodic lam α₀ (maProcess_ergodic θ hee he_meas) (maProcess_aemeasurable θ he_meas)

/-- **Hansen Theorem 14.25 (ergodicity, i.i.d. corollary).** If the innovations are i.i.d. (rather
than merely stationary ergodic white noise), the ARMA(p, q) process is ergodic — the i.i.d.
innovations are ergodic by `IsErgodicProcess.of_iid` (Hansen Theorem 14.4). -/
theorem armaProcess_ergodic_of_iid {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (θ : Fin (q + 1) → ℝ) (α₀ : ℝ)
    (he_indep : iIndepFun e P) (he_ident : ∀ t s, IdentDistrib (e t) (e s) P P)
    (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsErgodicProcess (armaProcess lam θ α₀ e) P :=
  armaProcess_ergodic lam θ α₀ (IsErgodicProcess.of_iid he_indep he_ident he_meas) he_meas

/-- **Hansen Theorem 14.25 (the ARMA recursion holds a.s.).** The ARMA(p, q) solution satisfies the
ARMA recursion `Yₜ = α₀ + ∑ᵢ αᵢ Yₜ₋ᵢ + uₜ` for almost every `ω`, with `uₜ = maProcess θ e t` the
finite MA innovation. This is `arProcess_recursion` applied to the innovation `maProcess θ e`: the
process defined as the AR(p) MA(∞) solution driven by `uₜ` is genuinely a solution of the ARMA
recursion. Requires the root condition (all `‖λᵢ‖ < 1`) and conjugation closure of the reciprocal
roots (the `σ` hypothesis), exactly as for `arProcess_recursion`. -/
theorem armaProcess_recursion {e : ℤ → Ω → ℝ} (lam : Fin p → ℂ) (θ : Fin (q + 1) → ℝ) (α₀ : ℝ)
    (hlam : ∀ i, ‖lam i‖ < 1) (σ : Equiv.Perm (Fin p))
    (hσ : ∀ i, lam (σ i) = starRingEnd ℂ (lam i))
    (he : IsStrictlyStationary e P) (he_meas : ∀ t, AEMeasurable (e t) P)
    (he_int : Integrable (e 0) P) (t : ℤ) :
    ∀ᵐ ω ∂P, armaProcess lam θ α₀ e t ω
      = α₀ + ∑ i : Fin p, arPolyCoeff lam ((i : ℕ) + 1)
          * armaProcess lam θ α₀ e (t - (((i : ℕ) : ℤ) + 1)) ω + maProcess θ e t ω :=
  arProcess_recursion lam α₀ hlam σ hσ (maProcess_strictlyStationary θ he he_meas)
    (maProcess_aemeasurable θ he_meas) (maProcess_integrable θ he he_int) t

end ProbabilityTheory

