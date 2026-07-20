import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Moments.Covariance

/-!
# Chapter 14: Martingale Difference Sequences

This file formalizes Hansen §14.10 on martingale difference sequences (MDS). The information
filtration is modelled by `MeasureTheory.Filtration ℤ m`; using `ℤ` as the time index keeps
the offsets `t - 1` and `t - k` clean. A process is `e : ℤ → Ω → ℝ`.

## Main declarations

* `ProbabilityTheory.IsMDS` — **Hansen Definition 14.4** (martingale difference sequence). A
  process `e` is an MDS relative to a filtration `ℱ` if it is adapted, integrable, and its
  one-step-ahead conditional expectation vanishes, `E[eₜ | ℱₜ₋₁] = 0` a.e.
* `ProbabilityTheory.IsMDS.integral_eq_zero` — an MDS has mean zero, `E[eₜ] = 0`. This is the
  unconditional consequence of the defining `E[eₜ | ℱₜ₋₁] = 0`, obtained via the tower law
  `MeasureTheory.integral_condExp`.
* `ProbabilityTheory.IsMDS.covariance_eq_zero` — **Hansen Theorem 14.10**: a square-integrable
  MDS is serially uncorrelated, `cov(eₜ, eₜ₋ₖ) = 0` for every lag `k ≥ 1`. (A square-integrable
  MDS is therefore white noise in the sense of Hansen §14.10.)

The proof of Theorem 14.10 rests on the conditional-expectation pull-out
`MeasureTheory.condExp_mul_of_stronglyMeasurable_right`: the past factor `eₜ₋ₖ` is
`ℱₜ₋₁`-measurable (since `t - k ≤ t - 1` for `k ≥ 1`) and so leaves the inner conditional
expectation `E[eₜ | ℱₜ₋₁] = 0`, killing the product.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℤ m} {e : ℤ → Ω → ℝ}

/-- **Hansen Definition 14.4 — martingale difference sequence.**

A real-valued process `e : ℤ → Ω → ℝ` is a *martingale difference sequence* (MDS) with respect
to the information filtration `ℱ : Filtration ℤ m` under `P` if:

* `adapted` — `e` is adapted to `ℱ`, i.e. each `eₜ` is `ℱₜ`-measurable, so `ℱₜ` carries at least
  the information in the history `(…, eₜ₋₁, eₜ)`;
* `integrable` — each `eₜ` is integrable, so the conditional expectation below is defined;
* `condExp_eq_zero` — the defining property `E[eₜ | ℱₜ₋₁] = 0` a.e. for every `t`.

The defining property says the best forecast of `eₜ` given the past information `ℱₜ₋₁` is `0`.
A martingale `Mₜ` has martingale differences `eₜ = Mₜ - Mₜ₋₁`. -/
structure IsMDS (ℱ : Filtration ℤ m) (e : ℤ → Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Each `eₜ` is `ℱₜ`-measurable (the process is adapted to the information filtration). -/
  adapted : Adapted ℱ e
  /-- Each `eₜ` is integrable. -/
  integrable : ∀ t, Integrable (e t) P
  /-- The defining MDS property: `E[eₜ | ℱₜ₋₁] = 0` a.e. -/
  condExp_eq_zero : ∀ t, P[e t | ℱ (t - 1)] =ᵐ[P] 0

namespace IsMDS

/-- **Hansen §14.10 — an MDS has mean zero.** Taking unconditional expectations of the defining
property `E[eₜ | ℱₜ₋₁] = 0` gives `E[eₜ] = 0`.

The integral of `eₜ` equals the integral of its conditional expectation by the tower law
`MeasureTheory.integral_condExp` (valid since `ℱₜ₋₁ ≤ m`), and that conditional expectation is
a.e. `0`. -/
theorem integral_eq_zero (h : IsMDS ℱ e P) (t : ℤ) : ∫ ω, e t ω ∂P = 0 := by
  calc
    ∫ ω, e t ω ∂P = ∫ ω, (P[e t | ℱ (t - 1)]) ω ∂P := (integral_condExp (ℱ.le (t - 1))).symm
    _ = ∫ ω, (0 : Ω → ℝ) ω ∂P := integral_congr_ae (h.condExp_eq_zero t)
    _ = 0 := by simp

omit [IsProbabilityMeasure P] in
/-- The lag-`k` past value `eₜ₋ₖ` is `ℱₜ₋₁`-strongly-measurable whenever `k ≥ 1`.

This is the strong-measurability bridge needed to pull `eₜ₋ₖ` out of the conditional
expectation `E[· | ℱₜ₋₁]`: adaptedness gives `ℱₜ₋ₖ`-measurability, real-valuedness upgrades it
to strong measurability, and `t - k ≤ t - 1` lets the filtration monotonicity widen the
sigma-algebra to `ℱₜ₋₁`. -/
private theorem stronglyMeasurable_past (h : IsMDS ℱ e P) {t k : ℤ} (hk : 1 ≤ k) :
    StronglyMeasurable[ℱ (t - 1)] (e (t - k)) :=
  (h.adapted (t - k)).stronglyMeasurable.mono (ℱ.mono (by omega))

/-- **Hansen Theorem 14.10 — a square-integrable MDS is serially uncorrelated.**

If `e` is a martingale difference sequence with respect to `ℱ` and each `eₜ` is square-integrable
(`MemLp (eₜ) 2 P`), then the autocovariances at all nonzero lags vanish:
`cov(eₜ, eₜ₋ₖ) = 0` for every `k ≥ 1`. Equivalently, a square-integrable MDS is white noise.

Proof outline.
* Both means vanish (`IsMDS.integral_eq_zero`), so by `ProbabilityTheory.covariance_eq_sub`
  the covariance reduces to the mixed second moment `cov(eₜ, eₜ₋ₖ) = E[eₜ · eₜ₋ₖ]`.
* By the tower law that moment equals `E[ E[eₜ · eₜ₋ₖ | ℱₜ₋₁] ]`.
* The past factor `eₜ₋ₖ` is `ℱₜ₋₁`-measurable (since `k ≥ 1`), so it pulls out of the inner
  conditional expectation (`MeasureTheory.condExp_mul_of_stronglyMeasurable_right`), leaving
  `E[eₜ · eₜ₋ₖ | ℱₜ₋₁] = E[eₜ | ℱₜ₋₁] · eₜ₋ₖ = 0 · eₜ₋ₖ = 0` a.e.
* Hence the moment is `E[0] = 0`. -/
theorem covariance_eq_zero (h : IsMDS ℱ e P) (hL2 : ∀ t, MemLp (e t) 2 P) {t k : ℤ}
    (hk : 1 ≤ k) : covariance (e t) (e (t - k)) P = 0 := by
  -- Integrability of the cross product `eₜ · eₜ₋ₖ`.
  have hprod_int : Integrable (e t * e (t - k)) P := (hL2 t).integrable_mul (hL2 (t - k))
  -- Reduce the covariance to the mixed second moment using mean-zero of both factors.
  rw [covariance_eq_sub (hL2 t) (hL2 (t - k)), h.integral_eq_zero t, h.integral_eq_zero (t - k)]
  simp only [mul_zero, sub_zero]
  -- `eₜ₋ₖ` pulls out of `E[· | ℱₜ₋₁]`, leaving `E[eₜ | ℱₜ₋₁] · eₜ₋ₖ`, which is a.e. `0`.
  have hpull : P[e t * e (t - k) | ℱ (t - 1)] =ᵐ[P] 0 := by
    refine (condExp_mul_of_stronglyMeasurable_right (h.stronglyMeasurable_past hk) hprod_int
      (h.integrable t)).trans ?_
    refine (h.condExp_eq_zero t).mono fun ω hω => ?_
    simp [Pi.mul_apply, hω]
  -- The mixed moment is the integral of this conditional expectation, hence `0`.
  calc
    ∫ ω, (e t * e (t - k)) ω ∂P
        = ∫ ω, (P[e t * e (t - k) | ℱ (t - 1)]) ω ∂P := (integral_condExp (ℱ.le (t - 1))).symm
    _ = ∫ ω, (0 : Ω → ℝ) ω ∂P := integral_congr_ae hpull
    _ = 0 := by simp

end IsMDS

end ProbabilityTheory
