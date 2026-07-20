import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Chapter 14: Time Series — AR polynomial inversion (Hansen Theorem 14.24)

This file formalizes the purely analytic/combinatorial content of Hansen's *Econometrics*
Theorem 14.24 (the moving-average coefficient bound for an inverted autoregressive polynomial).
No probability is involved.

## Mathematical statement

If all roots `rⱼ` of the AR polynomial `α(z) = 1 - α₁ z - ⋯ - αₚ zᵖ` satisfy `|rⱼ| > 1`, then
`b(z) = α(z)⁻¹ = ∑ⱼ bⱼ zʲ` has coefficients bounded by `|bⱼ| ≤ (j + 1)ᵖ λʲ` and the series
`∑ⱼ |bⱼ|` converges, where `λ = maxⱼ |rⱼ⁻¹| < 1`.

## Formalization design (self-contained — avoids power-series inversion)

Factor `α(z) = ∏ᵢ (1 - λᵢ z)` with `λᵢ = rᵢ⁻¹` the *reciprocal roots*, each `‖λᵢ‖ ≤ Λ < 1`
(the root condition `|rⱼ| > 1` enters exactly as `‖λᵢ‖ = |rⱼ⁻¹| ≤ Λ < 1`). The inverse is the
product of geometric series

`b(z) = ∏ᵢ 1 / (1 - λᵢ z) = ∏ᵢ ∑ₖ (λᵢ z)ᵏ`,

whose `zʲ` coefficient is the convolution

`bⱼ = ∑_{k₁ + ⋯ + kₚ = j} ∏ᵢ λᵢ^{kᵢ}`.

We *define* `arInverseCoeff` by this explicit composition-sum (the geometric-convolution `zʲ`
coefficient), so the result is self-contained and does not need to be derived from a
`PowerSeries.inv`. The composition index set is `Finset.Nat.antidiagonalTuple p j`, the finset of
`f : Fin p → ℕ` with `∑ i, f i = j`.

## Main declarations

* `HansenTimeSeries.arInverseCoeff` — the geometric-convolution coefficient `bⱼ`.
* `HansenTimeSeries.norm_arInverseCoeff_le` — **Hansen Theorem 14.24 (coefficient bound).**
  `‖bⱼ‖ ≤ (j + 1)ᵖ Λʲ`.
* `HansenTimeSeries.summable_arInverseCoeff` — **Hansen Theorem 14.24 (summability).**
  `∑ⱼ ‖bⱼ‖ < ∞`, i.e. `Summable (fun j => ‖bⱼ‖)`.
* `HansenTimeSeries.arInverseCoeff_mul_arPoly` — **Hansen Theorem 14.24 (power-series identity).**
  The generating series `b(z) = ∑ⱼ bⱼ zʲ` of the coefficients is a genuine two-sided inverse of the
  factored AR polynomial: `b(z) · ∏ᵢ (1 - λᵢ z) = 1` in `ℂ⟦X⟧`.
* `HansenTimeSeries.mk_arInverseCoeff_eq_inv` — the same fact in inverse form,
  `b(z) = (∏ᵢ (1 - λᵢ z))⁻¹`, identifying `arInverseCoeff` with the formal-power-series inverse
  of the AR polynomial.

The last two theorems justify the name `arInverseCoeff`: the combinatorial composition-sum `bⱼ`
really is the `zʲ` coefficient of `α(z)⁻¹`. The identity is proved at the level of formal power
series (no convergence needed) by factoring `α(z) = ∏ᵢ (1 - λᵢ z)`, inverting each degree-one
factor with the geometric series `∑ₙ λⁿ zⁿ`, and matching the product's coefficients to the
`antidiagonalTuple` convolution defining `arInverseCoeff`.
-/

open scoped BigOperators

namespace HansenTimeSeries

variable {p : ℕ}

/-- The `zʲ` coefficient `bⱼ` of the inverted AR polynomial `α(z)⁻¹ = ∏ᵢ 1 / (1 - λᵢ z)`, defined
explicitly as the geometric-convolution sum `bⱼ = ∑_{k₁ + ⋯ + kₚ = j} ∏ᵢ λᵢ^{kᵢ}` over the
`p`-tuples of naturals summing to `j`. Here `λ i = rᵢ⁻¹` are the reciprocal roots of the AR
polynomial; the root condition `|rᵢ| > 1` will be used as `‖λ i‖ ≤ Λ < 1`. See Hansen
Theorem 14.24. -/
noncomputable def arInverseCoeff (lam : Fin p → ℂ) (j : ℕ) : ℂ :=
  ∑ f ∈ Finset.Nat.antidiagonalTuple p j, ∏ i, lam i ^ f i

/-- Each composition term `∏ i, ‖λ i‖ ^ f i` of a tuple `f` summing to `j` is bounded by `Λʲ`,
provided `0 ≤ Λ` and `‖λ i‖ ≤ Λ` for all `i`. -/
private lemma prod_norm_pow_le {lam : Fin p → ℂ} {Λ : ℝ}
    (hlam : ∀ i, ‖lam i‖ ≤ Λ) {j : ℕ} {f : Fin p → ℕ}
    (hf : f ∈ Finset.Nat.antidiagonalTuple p j) :
    ∏ i, ‖lam i‖ ^ f i ≤ Λ ^ j := by
  have hsum : ∑ i, f i = j := Finset.Nat.mem_antidiagonalTuple.mp hf
  calc ∏ i, ‖lam i‖ ^ f i
      ≤ ∏ i, Λ ^ f i :=
        Finset.prod_le_prod (fun i _ => pow_nonneg (norm_nonneg _) _)
          (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hlam i) _)
    _ = Λ ^ ∑ i, f i := Finset.prod_pow_eq_pow_sum _ _ _
    _ = Λ ^ j := by rw [hsum]

/-- The number of `p`-tuples of naturals summing to `j` is at most `(j + 1)ᵖ`: each such tuple `f`
satisfies `f i ≤ j`, so the identity map injects the index set into
`Fintype.piFinset (fun _ => Finset.range (j + 1))`, a finset of cardinality `(j + 1)ᵖ`. -/
private lemma card_antidiagonalTuple_le (p j : ℕ) :
    (Finset.Nat.antidiagonalTuple p j).card ≤ (j + 1) ^ p := by
  have hmem : ∀ f ∈ Finset.Nat.antidiagonalTuple p j, ∀ i, f i ≤ j := by
    intro f hf i
    have hsum : ∑ k, f k = j := Finset.Nat.mem_antidiagonalTuple.mp hf
    calc f i ≤ ∑ k, f k := Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = j := hsum
  -- The identity map injects the index set into `piFinset (fun _ => range (j + 1))`.
  have hcard : (Finset.Nat.antidiagonalTuple p j).card ≤
      (Fintype.piFinset (fun _ : Fin p => Finset.range (j + 1))).card := by
    refine Finset.card_le_card_of_injOn (fun f => f) (fun f hf => ?_) (fun _ _ _ _ h => h)
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range] at hf ⊢
    exact fun i => Nat.lt_succ_of_le (hmem f hf i)
  calc (Finset.Nat.antidiagonalTuple p j).card
      ≤ (Fintype.piFinset (fun _ : Fin p => Finset.range (j + 1))).card := hcard
    _ = (j + 1) ^ p := by
        rw [Fintype.card_piFinset]
        simp

/-- **Hansen Theorem 14.24 (coefficient bound).** With reciprocal roots `λ : Fin p → ℂ` all of
norm `≤ Λ` (so `0 ≤ Λ`), the geometric-convolution coefficient `bⱼ = arInverseCoeff λ j` of the
inverted AR polynomial satisfies `‖bⱼ‖ ≤ (j + 1)ᵖ Λʲ`. The root condition `|rᵢ| > 1` enters as
`‖λ i‖ = |rᵢ⁻¹| ≤ Λ < 1`; here only `‖λ i‖ ≤ Λ` and `0 ≤ Λ` are needed for the bound. -/
theorem norm_arInverseCoeff_le {lam : Fin p → ℂ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlam : ∀ i, ‖lam i‖ ≤ Λ) (j : ℕ) :
    ‖arInverseCoeff lam j‖ ≤ ((j : ℝ) + 1) ^ p * Λ ^ j := by
  have hterm : ∀ f ∈ Finset.Nat.antidiagonalTuple p j, ‖∏ i, lam i ^ f i‖ ≤ Λ ^ j := by
    intro f hf
    rw [norm_prod]
    refine le_trans (le_of_eq ?_) (prod_norm_pow_le hlam hf)
    exact Finset.prod_congr rfl (fun i _ => norm_pow _ _)
  calc ‖arInverseCoeff lam j‖
      ≤ ∑ f ∈ Finset.Nat.antidiagonalTuple p j, ‖∏ i, lam i ^ f i‖ :=
        norm_sum_le _ _
    _ ≤ (Finset.Nat.antidiagonalTuple p j).card • Λ ^ j :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (Finset.Nat.antidiagonalTuple p j).card * Λ ^ j := by rw [nsmul_eq_mul]
    _ ≤ ((j + 1) ^ p : ℕ) * Λ ^ j := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hΛ _)
        exact_mod_cast card_antidiagonalTuple_le p j
    _ = ((j : ℝ) + 1) ^ p * Λ ^ j := by push_cast; ring

/-- The majorant `j ↦ ((j : ℝ) + 1)ᵖ Λʲ` is summable for `0 ≤ Λ < 1`. We compare it to a shifted
`pow × geometric` series with ratio `r = (1 + Λ) / 2 ∈ [1/2, 1)`, which is summable by
`summable_pow_mul_geometric_of_norm_lt_one` together with `summable_nat_add_iff`. -/
private lemma summable_coeff_majorant {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ p * Λ ^ j) := by
  set r : ℝ := (1 + Λ) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrlt : r < 1 := by rw [hr]; linarith
  have hΛr : Λ ≤ r := by rw [hr]; linarith
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hrpos.le]; exact hrlt
  -- `Summable (fun n => (n : ℝ) ^ p * r ^ n)`.
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ p * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one p hnorm
  -- Shift by one and divide by `r` to land on `(j + 1) ^ p * r ^ j`.
  have hshift : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ p * r ^ j) := by
    have h1 : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ p * r ^ (j + 1)) :=
      (summable_nat_add_iff 1).mpr hgeo
    have h2 : Summable (fun j : ℕ => r⁻¹ * (((j + 1 : ℕ) : ℝ) ^ p * r ^ (j + 1))) :=
      h1.mul_left r⁻¹
    refine h2.congr (fun j => ?_)
    have hr0 : r ≠ 0 := ne_of_gt hrpos
    have hpow : r ^ (j + 1) = r * r ^ j := by rw [pow_succ]; ring
    rw [hpow]
    push_cast
    rw [← mul_assoc, ← mul_assoc, mul_comm r⁻¹ _, mul_assoc _ r⁻¹ r, inv_mul_cancel₀ hr0,
      mul_one]
  -- Compare the `Λ`-majorant against the `r`-majorant.
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hshift
  · positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ hΛ0 hΛr j

/-- **Hansen Theorem 14.24 (summability).** With reciprocal roots `λ : Fin p → ℂ` all of norm
`≤ Λ < 1`, the absolute moving-average coefficients `‖bⱼ‖` of the inverted AR polynomial are
summable: `∑ⱼ ‖bⱼ‖ < ∞`. This is the absolute convergence of the MA(∞) representation. The root
condition `|rᵢ| > 1` enters as `‖λ i‖ = |rᵢ⁻¹| ≤ Λ < 1`. -/
theorem summable_arInverseCoeff {lam : Fin p → ℂ} {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1)
    (hlam : ∀ i, ‖lam i‖ ≤ Λ) :
    Summable (fun j : ℕ => ‖arInverseCoeff lam j‖) := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => norm_arInverseCoeff_le hΛ0 hlam j) ?_
  exact summable_coeff_majorant hΛ0 hΛ1

/-- Per-factor power-series identity: the geometric series `∑ₙ λⁿ zⁿ` inverts the degree-one factor
`1 - λ z`. This is the AR(1) inversion `(1 - λ z)⁻¹ = ∑ₙ λⁿ zⁿ` at the level of formal power series,
proved by coefficient extraction. No hypothesis on `λ` is needed (the case `λ = 0` is included). -/
private lemma geom_mul_one_sub (lam : ℂ) :
    (PowerSeries.mk fun n => lam ^ n) * (1 - PowerSeries.C lam * PowerSeries.X) = 1 := by
  have hexpand :
      (PowerSeries.mk fun n => lam ^ n) * (1 - PowerSeries.C lam * PowerSeries.X)
        = (PowerSeries.mk fun n => lam ^ n)
          - PowerSeries.C lam * ((PowerSeries.mk fun n => lam ^ n) * PowerSeries.X) := by
    ring
  rw [hexpand]
  refine PowerSeries.ext fun n => ?_
  rw [map_sub, PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_mul_X, mul_zero, sub_zero, PowerSeries.coeff_mk]
    simp
  | succ m =>
    rw [PowerSeries.coeff_succ_mul_X]
    simp only [PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_one, if_neg (by omega)]
    ring

/-- The generating power series of the geometric-convolution coefficients `arInverseCoeff` is the
product of the per-root geometric series: `∑ⱼ bⱼ zʲ = ∏ᵢ (∑ₙ λᵢⁿ zⁿ)`. Coefficients are matched via
`PowerSeries.coeff_prod`, reindexing its `finsuppAntidiag` sum to the `antidiagonalTuple` sum
defining `arInverseCoeff` through `Finsupp.equivFunOnFinite`. -/
lemma mk_arInverseCoeff_eq_prod (lam : Fin p → ℂ) :
    (PowerSeries.mk fun j => arInverseCoeff lam j)
      = ∏ i, PowerSeries.mk (fun n => lam i ^ n) := by
  refine PowerSeries.ext fun d => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_prod]
  simp only [PowerSeries.coeff_mk]
  unfold arInverseCoeff
  refine Finset.sum_bij' (fun f _ => Finsupp.equivFunOnFinite.symm f)
    (fun l _ => (l : Fin p → ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.Nat.mem_antidiagonalTuple] at hf
    simpa [Finset.mem_finsuppAntidiag, Finsupp.coe_equivFunOnFinite_symm] using hf
  · intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    simpa [Finset.Nat.mem_antidiagonalTuple] using hl.1
  · intro f _
    exact Finsupp.coe_equivFunOnFinite_symm f
  · intro l _
    exact Finsupp.equivFunOnFinite_symm_coe l
  · intro f _
    simp only [Finsupp.coe_equivFunOnFinite_symm]

/-- **Hansen Theorem 14.24 (power-series identity).** The generating series
`b(z) = ∑ⱼ arInverseCoeff λ j · zʲ` is a two-sided inverse of the factored AR polynomial
`α(z) = ∏ᵢ (1 - λᵢ z)`: `b(z) · α(z) = 1` in `ℂ⟦X⟧`. Here `λ i = rᵢ⁻¹` are the reciprocal roots;
the identity is purely formal and needs no root condition. -/
theorem arInverseCoeff_mul_arPoly (lam : Fin p → ℂ) :
    (PowerSeries.mk fun j => arInverseCoeff lam j) *
      ∏ i, (1 - PowerSeries.C (lam i) * PowerSeries.X) = 1 := by
  rw [mk_arInverseCoeff_eq_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => geom_mul_one_sub (lam i)

/-- **Hansen Theorem 14.24 (inverse form).** The generating series of `arInverseCoeff` is the
formal-power-series inverse of the factored AR polynomial: `b(z) = (∏ᵢ (1 - λᵢ z))⁻¹`. This
identifies the combinatorial composition-sum coefficients `bⱼ` with the coefficients of `α(z)⁻¹`,
justifying the name `arInverseCoeff`. The AR polynomial has constant coefficient `1 ≠ 0`, so it is
invertible in `ℂ⟦X⟧`. -/
theorem mk_arInverseCoeff_eq_inv (lam : Fin p → ℂ) :
    (PowerSeries.mk fun j => arInverseCoeff lam j)
      = (∏ i, (1 - PowerSeries.C (lam i) * PowerSeries.X))⁻¹ := by
  have hne : PowerSeries.constantCoeff (R := ℂ)
      (∏ i, (1 - PowerSeries.C (lam i) * PowerSeries.X)) ≠ 0 := by
    have hconst : PowerSeries.constantCoeff (R := ℂ)
        (∏ i, (1 - PowerSeries.C (lam i) * PowerSeries.X)) = 1 := by
      rw [map_prod]
      refine Finset.prod_eq_one fun i _ => ?_
      simp
    rw [hconst]; exact one_ne_zero
  rw [PowerSeries.eq_inv_iff_mul_eq_one hne]
  exact arInverseCoeff_mul_arPoly lam

/-- **Realness of the MA(∞) coefficients.** If the reciprocal roots are closed under complex
conjugation — encoded by a permutation `σ` of the index set with `lam (σ i) = conj (lam i)` — then
every coefficient `arInverseCoeff lam j` is fixed by complex conjugation, hence real. This is the
case of an AR polynomial with real coefficients, whose (possibly complex) reciprocal roots pair up
into conjugate pairs; it is used by AR(p) with real coefficients (Hansen Theorem 14.23). The proof
conjugates the composition-sum term by term (`conj` is a ring homomorphism) and reindexes both the
inner product over roots and the outer sum over compositions by `σ`. -/
theorem starRingEnd_arInverseCoeff (lam : Fin p → ℂ) (σ : Equiv.Perm (Fin p))
    (hσ : ∀ i, lam (σ i) = starRingEnd ℂ (lam i)) (j : ℕ) :
    starRingEnd ℂ (arInverseCoeff lam j) = arInverseCoeff lam j := by
  unfold arInverseCoeff
  rw [map_sum]
  refine Finset.sum_nbij' (fun f k => f (σ.symm k)) (fun g k => g (σ k)) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.Nat.mem_antidiagonalTuple] at hf ⊢
    rw [Equiv.sum_comp σ.symm f]; exact hf
  · intro g hg
    rw [Finset.Nat.mem_antidiagonalTuple] at hg ⊢
    rw [Equiv.sum_comp σ g]; exact hg
  · intro f _
    funext k; simp only [Equiv.symm_apply_apply]
  · intro g _
    funext k; simp only [Equiv.apply_symm_apply]
  · intro f _
    rw [map_prod, ← Equiv.prod_comp σ (fun k => lam k ^ f (σ.symm k))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_pow, ← hσ i, Equiv.symm_apply_apply]

end HansenTimeSeries
