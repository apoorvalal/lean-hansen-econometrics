import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Chapter 14: Time Series — deterministic supporting results

This file formalizes the purely deterministic (real/complex analysis and algebra) supporting
results behind Hansen's *Econometrics* Chapter 14 (Time Series). None of these statements involve
probability; they are the analytic facts the chapter relies on.

## Main declarations

* `HansenTimeSeries.tsum_geometric_eq` — **Hansen Theorem 14.20.** For real `β` with `|β| < 1`,
  the geometric series `∑' k, β ^ k` sums to `(1 - β)⁻¹`.
* `HansenTimeSeries.tendsto_sum_pow_rpow` — **Hansen Theorem 14.36.** The normalized power sum
  `n ^ (-(1+r)) * ∑_{t<n} (t+1) ^ r` converges to `1 / (1 + r)` for `r > 0`, the continuous-time
  Riemann-sum limit behind time-trend regressions.
* `HansenTimeSeries.charpoly_companion_ar2` — **Hansen Theorem 14.22 (companion form).** The 2×2
  AR(2) companion matrix has characteristic polynomial `λ ^ 2 - α₁ λ - α₂`.
* `HansenTimeSeries.jury_conditions_iff_stationarity_triangle` — **Hansen (14.35)–(14.37).** The
  degree-2 Jury conditions `|α₂| < 1 ∧ |α₁| < 1 - α₂` are equivalent to the stationarity triangle.
* `HansenTimeSeries.ar2_roots_in_unit_disk_iff` — **Hansen Theorem 14.22(a).** Both roots of the
  AR(2) characteristic polynomial have modulus `< 1` iff `(α₁, α₂)` lies in the stationarity
  triangle `α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ α₂ > -1`.
-/

open scoped Topology

open Filter

namespace HansenTimeSeries

/-- **Hansen Theorem 14.20.** For a real ratio `β` with `|β| < 1`, the geometric series
`∑' k, β ^ k` converges to `(1 - β)⁻¹`. This is the scalar geometric-series identity behind the
MA(∞) representation of a stationary AR(1) process. -/
theorem tsum_geometric_eq (β : ℝ) (hβ : |β| < 1) : ∑' k : ℕ, β ^ k = (1 - β)⁻¹ := by
  have h : ‖β‖ < 1 := by rwa [Real.norm_eq_abs]
  exact tsum_geometric_of_norm_lt_one h

/-- The integral of `x ^ r` over `[0, n]` equals `n ^ (1 + r) / (1 + r)` for `0 < r`. -/
private lemma integral_rpow_zero_to (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∫ x in (0 : ℝ)..(n : ℝ), x ^ r = (n : ℝ) ^ (1 + r) / (1 + r) := by
  rw [integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith)]
  ring_nf

/-- The integral of `x ^ r` over `[1, n+1]` equals `((n+1) ^ (1 + r) - 1) / (1 + r)`. -/
private lemma integral_rpow_one_to (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∫ x in (1 : ℝ)..(1 + (n : ℝ)), x ^ r = ((1 + (n : ℝ)) ^ (1 + r) - 1) / (1 + r) := by
  rw [integral_rpow (Or.inl (by linarith))]
  rw [Real.one_rpow]
  ring_nf

/-- `(fun x => x ^ r)` is monotone on `Set.Icc a b` for `0 ≤ a` and `0 ≤ r`. -/
private lemma monotoneOn_rpow_Icc (r : ℝ) (hr : 0 ≤ r) (a b : ℝ) (ha : 0 ≤ a) :
    MonotoneOn (fun x : ℝ => x ^ r) (Set.Icc a b) :=
  (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hr).mono
    (fun _ hx => le_trans ha hx.1)

/-- Lower bound: the integral over `[0, n]` is below the power sum `∑_{t<n} (t+1) ^ r`. -/
private lemma integral_le_sum_rpow (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (n : ℝ) ^ (1 + r) / (1 + r) ≤ ∑ t ∈ Finset.range n, ((t : ℝ) + 1) ^ r := by
  have hmono : MonotoneOn (fun x : ℝ => x ^ r) (Set.Icc (0 : ℝ) (0 + (n : ℝ))) :=
    monotoneOn_rpow_Icc r hr.le 0 _ le_rfl
  have hle := hmono.integral_le_sum
  rw [zero_add] at hle
  rw [integral_rpow_zero_to r hr n] at hle
  refine le_trans hle (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  ring_nf

/-- Upper bound: the power sum `∑_{t<n} (t+1) ^ r` is below the integral over `[1, n+1]`. -/
private lemma sum_le_integral_rpow (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∑ t ∈ Finset.range n, ((t : ℝ) + 1) ^ r ≤ ((1 + (n : ℝ)) ^ (1 + r) - 1) / (1 + r) := by
  have hmono : MonotoneOn (fun x : ℝ => x ^ r) (Set.Icc (1 : ℝ) (1 + (n : ℝ))) :=
    monotoneOn_rpow_Icc r hr.le 1 _ zero_le_one
  have hle := hmono.sum_le_integral
  rw [integral_rpow_one_to r hr n] at hle
  refine le_trans (le_of_eq ?_) hle
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring_nf

/-- For `0 < r` and `n ≥ 1`, the lower envelope `n ^ (-(1+r)) * (n ^ (1+r) / (1+r))` collapses to
the constant `1 / (1 + r)`. -/
private lemma rpow_neg_mul_lower (r : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(1 + r)) * ((n : ℝ) ^ (1 + r) / (1 + r)) = 1 / (1 + r) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  rw [div_eq_mul_inv, ← mul_assoc, ← Real.rpow_add hnpos]
  simp

/-- For `0 < r` and `n ≥ 1`, the upper envelope rewrites as the displayed ratio of an
`rpow` of `(1+n)/n` and the vanishing tail `n ^ (-(1+r))`. -/
private lemma rpow_neg_mul_upper (r : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(1 + r)) * (((1 + (n : ℝ)) ^ (1 + r) - 1) / (1 + r)) =
      (((1 + (n : ℝ)) / (n : ℝ)) ^ (1 + r) - (n : ℝ) ^ (-(1 + r))) / (1 + r) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hkey : (n : ℝ) ^ (-(1 + r)) * (1 + (n : ℝ)) ^ (1 + r) =
      ((1 + (n : ℝ)) / (n : ℝ)) ^ (1 + r) := by
    rw [Real.div_rpow (by positivity) hnpos.le, Real.rpow_neg hnpos.le, div_eq_mul_inv,
      mul_comm]
  rw [mul_div_assoc', ← hkey]
  ring

/-- The ratio `(1 + n) / n` tends to `1` along `atTop`. -/
private lemma tendsto_one_add_div_self :
    Tendsto (fun n : ℕ => (1 + (n : ℝ)) / (n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ (by norm_num)
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [inv_div, add_comm]

/-- The upper envelope `(((1+n)/n) ^ (1+r) - n ^ (-(1+r))) / (1+r)` tends to `1 / (1+r)`. -/
private lemma tendsto_upper_envelope (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun n : ℕ => (((1 + (n : ℝ)) / (n : ℝ)) ^ (1 + r) - (n : ℝ) ^ (-(1 + r))) / (1 + r))
      atTop (𝓝 (1 / (1 + r))) := by
  have h1 : Tendsto (fun n : ℕ => ((1 + (n : ℝ)) / (n : ℝ)) ^ (1 + r)) atTop (𝓝 1) := by
    have h := tendsto_one_add_div_self.rpow_const (p := 1 + r) (Or.inr (by linarith))
    rw [Real.one_rpow] at h
    exact h
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 + r))) atTop (𝓝 0) := by
    have hcomp := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 + r by linarith)).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp] using hcomp
  have hsub : Tendsto
      (fun n : ℕ => ((1 + (n : ℝ)) / (n : ℝ)) ^ (1 + r) - (n : ℝ) ^ (-(1 + r)))
      atTop (𝓝 (1 - 0)) := h1.sub h2
  have hfin := hsub.div_const (1 + r)
  simpa using hfin

/-- **Hansen Theorem 14.36.** For `r > 0`, the normalized power sum
`n ^ (-(1+r)) * ∑_{t<n} (t+1) ^ r` converges to `1 / (1 + r)`. This is the deterministic
Riemann-sum limit (equation 14.36) underpinning the asymptotics of polynomial time-trend
regressions: the time-trend power sum `∑_{t=1}^n t ^ r` grows like `n ^ (1+r) / (1+r)`. The proof
squeezes the sum between the integrals `∫₀ⁿ x ^ r dx` and `∫₁ⁿ⁺¹ x ^ r dx` of the monotone
integrand `x ↦ x ^ r`. -/
theorem tendsto_sum_pow_rpow (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 + r)) * ∑ t ∈ Finset.range n, ((t : ℝ) + 1) ^ r)
      Filter.atTop (nhds (1 / (1 + r))) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => 1 / (1 + r))
    (h := fun n : ℕ =>
      (((1 + (n : ℝ)) / (n : ℝ)) ^ (1 + r) - (n : ℝ) ^ (-(1 + r))) / (1 + r))
    tendsto_const_nhds (tendsto_upper_envelope r hr) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + r)) := Real.rpow_nonneg (by positivity) _
    have hlb := integral_le_sum_rpow r hr n
    calc 1 / (1 + r)
        = (n : ℝ) ^ (-(1 + r)) * ((n : ℝ) ^ (1 + r) / (1 + r)) :=
          (rpow_neg_mul_lower r hn).symm
      _ ≤ (n : ℝ) ^ (-(1 + r)) * ∑ t ∈ Finset.range n, ((t : ℝ) + 1) ^ r :=
          mul_le_mul_of_nonneg_left hlb hpos
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + r)) := Real.rpow_nonneg (by positivity) _
    have hub := sum_le_integral_rpow r hr n
    calc (n : ℝ) ^ (-(1 + r)) * ∑ t ∈ Finset.range n, ((t : ℝ) + 1) ^ r
        ≤ (n : ℝ) ^ (-(1 + r)) * (((1 + (n : ℝ)) ^ (1 + r) - 1) / (1 + r)) :=
          mul_le_mul_of_nonneg_left hub hpos
      _ = (((1 + (n : ℝ)) / (n : ℝ)) ^ (1 + r) - (n : ℝ) ^ (-(1 + r))) / (1 + r) :=
          rpow_neg_mul_upper r hn

/-! ## Hansen Theorem 14.22(a): AR(2) stationarity triangle (Jury criterion) -/

/-- **Hansen Theorem 14.22 (companion form).** The AR(2) companion matrix
`A = !![α₁, α₂; 1, 0]` has characteristic polynomial `det(λ • 1 - A) = λ ^ 2 - α₁ * λ - α₂`. The
eigenvalues of `A` are therefore the roots of `λ ^ 2 - α₁ λ - α₂`. Stated over an arbitrary
commutative ring so it specializes to both `ℝ` and `ℂ`. -/
theorem charpoly_companion_ar2 {R : Type*} [CommRing R] (α₁ α₂ lam : R) :
    (lam • (1 : Matrix (Fin 2) (Fin 2) R) - !![α₁, α₂; 1, 0]).det
      = lam ^ 2 - α₁ * lam - α₂ := by
  rw [show lam • (1 : Matrix (Fin 2) (Fin 2) R) - !![α₁, α₂; 1, 0]
        = !![lam - α₁, -α₂; -1, lam] from ?_]
  · rw [Matrix.det_fin_two_of]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

/-- **Hansen equations (14.35)–(14.37): the real Jury equivalence.** For real AR(2) coefficients
`α₁, α₂`, writing the characteristic polynomial as the monic quadratic `λ ^ 2 - α₁ λ - α₂` (so the
degree-2 Schur–Cohn / Jury conditions read `|−α₂| < 1 ∧ |−α₁| < 1 + (−α₂)`), the Jury conditions
are equivalent to Hansen's stationarity triangle `α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ α₂ > -1`. -/
theorem jury_conditions_iff_stationarity_triangle (α₁ α₂ : ℝ) :
    (|α₂| < 1 ∧ |α₁| < 1 - α₂) ↔ (α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ -1 < α₂) := by
  rw [abs_lt, abs_lt]
  constructor
  · rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h3, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- If a complex pair `z₁, z₂` has real sum `α₁` and real product `-α₂` (the Vieta data of the
monic quadratic `z ^ 2 - α₁ z - α₂`), then the pair is closed under complex conjugation:
`conj z₁` is either `z₁` or `z₂`. -/
private lemma conj_mem_pair_of_real_vieta {α₁ α₂ : ℝ} {z₁ z₂ : ℂ}
    (hsum : z₁ + z₂ = (α₁ : ℂ)) (hprod : z₁ * z₂ = ((-α₂ : ℝ) : ℂ)) :
    starRingEnd ℂ z₁ = z₁ ∨ starRingEnd ℂ z₁ = z₂ := by
  have hfac : (starRingEnd ℂ z₁ - z₁) * (starRingEnd ℂ z₁ - z₂) = 0 := by
    have hquad : starRingEnd ℂ z₁ ^ 2 - (α₁ : ℂ) * starRingEnd ℂ z₁ + ((-α₂ : ℝ) : ℂ) = 0 := by
      have : z₁ ^ 2 - (α₁ : ℂ) * z₁ + ((-α₂ : ℝ) : ℂ) = 0 := by
        rw [← hsum, ← hprod]; ring
      have hc := congrArg (starRingEnd ℂ) this
      simpa [map_add, map_sub, map_mul, map_pow, Complex.conj_ofReal] using hc
    have hexpand : (starRingEnd ℂ z₁ - z₁) * (starRingEnd ℂ z₁ - z₂)
        = starRingEnd ℂ z₁ ^ 2 - (z₁ + z₂) * starRingEnd ℂ z₁ + z₁ * z₂ := by ring
    rw [hexpand, hsum, hprod, hquad]
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Real-root case of the Jury equivalence: two **real** roots `x₁, x₂` of `λ ^ 2 - α₁ λ - α₂`
both lie in `(-1, 1)` iff Hansen's stationarity triangle holds. -/
private lemma ar2_real_roots_iff {α₁ α₂ x₁ x₂ : ℝ}
    (hsum : x₁ + x₂ = α₁) (hprod : x₁ * x₂ = -α₂) :
    (|x₁| < 1 ∧ |x₂| < 1) ↔ (α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ -1 < α₂) := by
  have hP1 : (1 - x₁) * (1 - x₂) = 1 - α₁ - α₂ := by
    linear_combination (-(1 : ℝ)) * hsum + hprod
  have hPm1 : (1 + x₁) * (1 + x₂) = 1 + α₁ - α₂ := by
    linear_combination hsum + hprod
  constructor
  · rintro ⟨hx1, hx2⟩
    rw [abs_lt] at hx1 hx2
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [hx1.1, hx1.2, hx2.1, hx2.2, hP1]
    · nlinarith [hx1.1, hx1.2, hx2.1, hx2.2, hPm1]
    · nlinarith [hx1.1, hx1.2, hx2.1, hx2.2]
  · rintro ⟨h1, h2, h3⟩
    have hp1pos : 0 < (1 - x₁) * (1 - x₂) := by rw [hP1]; linarith
    have hpm1pos : 0 < (1 + x₁) * (1 + x₂) := by rw [hPm1]; linarith
    have hprodlt : x₁ * x₂ < 1 := by rw [hprod]; linarith
    have hprodgt : -1 < x₁ * x₂ := by rw [hprod]; linarith
    constructor
    · rw [abs_lt]
      constructor <;> nlinarith [hp1pos, hpm1pos, hprodlt, hprodgt]
    · rw [abs_lt]
      constructor <;> nlinarith [hp1pos, hpm1pos, hprodlt, hprodgt]

/-- Conjugate-pair case of the Jury equivalence: a genuinely complex root `z` paired with its
conjugate `conj z` (with `z + conj z = α₁`, `z * conj z = -α₂`) satisfies `‖z‖ < 1` iff Hansen's
stationarity triangle holds. -/
private lemma ar2_conj_roots_iff {α₁ α₂ : ℝ} {z : ℂ}
    (hsum : z + starRingEnd ℂ z = (α₁ : ℂ)) (hprod : z * starRingEnd ℂ z = ((-α₂ : ℝ) : ℂ)) :
    ‖z‖ < 1 ↔ (α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ -1 < α₂) := by
  -- `‖z‖ ^ 2 = |α₂|`
  have hnsq : (‖z‖ ^ 2 : ℝ) = -α₂ := by
    have hmc := Complex.mul_conj z
    rw [hprod] at hmc
    have : (Complex.normSq z : ℝ) = (-α₂ : ℝ) := by exact_mod_cast hmc.symm
    rw [Complex.normSq_eq_norm_sq] at this; exact this
  have hnormsq : ‖z‖ ^ 2 = |α₂| := by
    rw [hnsq, abs_of_nonpos (by nlinarith [sq_nonneg ‖z‖, hnsq])]
  -- `1 - α₁ - α₂ = ‖1 - z‖ ^ 2`
  have hP1 : (1 - α₁ - α₂ : ℝ) = ‖1 - z‖ ^ 2 := by
    have hconj : (1 : ℂ) - starRingEnd ℂ z = starRingEnd ℂ (1 - z) := by
      simp [map_sub]
    have hmc := Complex.mul_conj (1 - z)
    have hval : (1 - z) * (1 - starRingEnd ℂ z) = ((1 - α₁ - α₂ : ℝ) : ℂ) := by
      have : (1 - z) * (1 - starRingEnd ℂ z)
          = 1 - (z + starRingEnd ℂ z) + z * starRingEnd ℂ z := by ring
      rw [this, hsum, hprod]; push_cast; ring
    rw [hconj, hmc] at hval
    have : Complex.normSq (1 - z) = (1 - α₁ - α₂ : ℝ) := by exact_mod_cast hval
    rw [← Complex.normSq_eq_norm_sq, this]
  -- `1 + α₁ - α₂ = ‖1 + z‖ ^ 2`
  have hPm1 : (1 + α₁ - α₂ : ℝ) = ‖1 + z‖ ^ 2 := by
    have hconj : (1 : ℂ) + starRingEnd ℂ z = starRingEnd ℂ (1 + z) := by
      simp [map_add]
    have hmc := Complex.mul_conj (1 + z)
    have hval : (1 + z) * (1 + starRingEnd ℂ z) = ((1 + α₁ - α₂ : ℝ) : ℂ) := by
      have : (1 + z) * (1 + starRingEnd ℂ z)
          = 1 + (z + starRingEnd ℂ z) + z * starRingEnd ℂ z := by ring
      rw [this, hsum, hprod]; push_cast; ring
    rw [hconj, hmc] at hval
    have : Complex.normSq (1 + z) = (1 + α₁ - α₂ : ℝ) := by exact_mod_cast hval
    rw [← Complex.normSq_eq_norm_sq, this]
  have hP1nonneg : 0 ≤ (1 - α₁ - α₂ : ℝ) := by rw [hP1]; positivity
  have hPm1nonneg : 0 ≤ (1 + α₁ - α₂ : ℝ) := by rw [hPm1]; positivity
  constructor
  · intro hz
    have hzsq : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z, hz]
    rw [hnormsq] at hzsq
    rw [abs_lt] at hzsq
    -- strictness of P1, Pm1: `z ≠ 1` and `z ≠ -1` since `‖z‖ < 1`
    have hzne1 : z ≠ 1 := by rintro rfl; simp at hz
    have hznem1 : z ≠ -1 := by rintro rfl; simp at hz
    have hP1pos : 0 < (1 - α₁ - α₂ : ℝ) := by
      rw [hP1]; have : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzne1)
      positivity
    have hPm1pos : 0 < (1 + α₁ - α₂ : ℝ) := by
      rw [hPm1]; have : (1 : ℂ) + z ≠ 0 := by
        intro h; apply hznem1; linear_combination h
      positivity
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    have hα₂lt : α₂ < 1 := by linarith
    have habs : |α₂| < 1 := by rw [abs_lt]; exact ⟨h3, hα₂lt⟩
    have hzsq : ‖z‖ ^ 2 < 1 := by rw [hnormsq]; exact habs
    nlinarith [norm_nonneg z, hzsq]

/-- **Hansen Theorem 14.22(a): AR(2) stationarity region.** Let `z₁, z₂ : ℂ` be the two roots of
the AR(2) characteristic polynomial `λ ^ 2 - α₁ λ - α₂` for real coefficients `α₁, α₂` (so they
satisfy the Vieta relations `z₁ + z₂ = α₁` and `z₁ z₂ = -α₂`). Both roots have modulus `< 1` — the
condition for a covariance-stationary AR(2) — if and only if `(α₁, α₂)` lies in Hansen's
stationarity triangle `α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ α₂ > -1` (equations 14.35–14.37). -/
theorem ar2_roots_in_unit_disk_iff (α₁ α₂ : ℝ) (z₁ z₂ : ℂ)
    (hsum : z₁ + z₂ = (α₁ : ℂ)) (hprod : z₁ * z₂ = ((-α₂ : ℝ) : ℂ)) :
    (‖z₁‖ < 1 ∧ ‖z₂‖ < 1) ↔ (α₁ + α₂ < 1 ∧ α₂ - α₁ < 1 ∧ -1 < α₂) := by
  rcases conj_mem_pair_of_real_vieta hsum hprod with hreal | hconj
  · -- `z₁` is real, hence so is `z₂`; reduce to the real-root case.
    have him1 : z₁.im = 0 := Complex.conj_eq_iff_im.mp hreal
    have hz1 : ((z₁.re : ℝ) : ℂ) = z₁ := by
      apply Complex.ext <;> simp [him1]
    have him2 : z₂.im = 0 := by
      have : z₂ = (α₁ : ℂ) - z₁ := by linear_combination hsum
      rw [this]; simp [him1]
    have hz2 : ((z₂.re : ℝ) : ℂ) = z₂ := by
      apply Complex.ext <;> simp [him2]
    have hsumr : z₁.re + z₂.re = α₁ := by
      have := congrArg Complex.re hsum; simpa using this
    have hprodr : z₁.re * z₂.re = -α₂ := by
      have hp := congrArg Complex.re hprod
      simp [him1, him2] at hp; linarith [hp]
    have hnorm1 : ‖z₁‖ = |z₁.re| := by
      conv_lhs => rw [← hz1]
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hnorm2 : ‖z₂‖ = |z₂.re| := by
      conv_lhs => rw [← hz2]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm1, hnorm2]
    exact ar2_real_roots_iff hsumr hprodr
  · -- `z₂ = conj z₁`; reduce to the conjugate-pair case.
    have hsum' : z₁ + starRingEnd ℂ z₁ = (α₁ : ℂ) := by rw [hconj]; exact hsum
    have hprod' : z₁ * starRingEnd ℂ z₁ = ((-α₂ : ℝ) : ℂ) := by rw [hconj]; exact hprod
    have hnorm2 : ‖z₂‖ = ‖z₁‖ := by rw [← hconj, Complex.norm_conj]
    rw [hnorm2, and_self]
    exact ar2_conj_roots_iff hsum' hprod'

end HansenTimeSeries
