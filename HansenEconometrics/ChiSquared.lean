import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.LConvolution
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory ProbabilityTheory

namespace HansenEconometrics

/-- The chi-squared distribution with `k` degrees of freedom, defined as
`Gamma(shape = k/2, rate = 1/2)`. -/
noncomputable def chiSquared (k : ℕ) : Measure ℝ :=
  gammaMeasure ((k : ℝ) / 2) (1 / 2 : ℝ)

@[simp] lemma chiSquared_eq (k : ℕ) :
    chiSquared k = gammaMeasure ((k : ℝ) / 2) (1 / 2 : ℝ) := rfl

lemma isProbabilityMeasure_chiSquared {k : ℕ} (hk : 0 < k) :
    IsProbabilityMeasure (chiSquared k) := by
  refine isProbabilityMeasure_gammaMeasure ?_ ?_
  · exact div_pos (Nat.cast_pos.mpr hk) (by norm_num)
  · norm_num

instance {k : ℕ} [Fact (0 < k)] : IsProbabilityMeasure (chiSquared k) :=
  isProbabilityMeasure_chiSquared (k := k) (Fact.out)

lemma chiSquared_gammaPDF_of_neg {k : ℕ} {x : ℝ} (hx : x < 0) :
    gammaPDF ((k : ℝ) / 2) (1 / 2 : ℝ) x = 0 :=
  gammaPDF_of_neg hx

@[simp] lemma chiSquared_one_eq :
    chiSquared 1 = gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ) := by
  simp [chiSquared]

lemma rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le (1 / 2 : ℝ)]
  rw [Real.sqrt_eq_rpow]

lemma gaussian_exp_at_sqrt_eq {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-(Real.sqrt x - 0) ^ 2 / (2 : ℝ)) = Real.exp (-(x / 2)) := by
  have hsq : (Real.sqrt x - 0) ^ 2 = x := by
    simpa [pow_two] using Real.sq_sqrt hx
  rw [hsq]
  congr 1
  ring

/-! ### Preimage of Iic under squaring -/

/-- For `t < 0`, no real squares into `Iic t`. -/
lemma sq_preimage_Iic_of_neg {t : ℝ} (ht : t < 0) :
    (fun x : ℝ => x ^ 2) ⁻¹' Set.Iic t = ∅ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
  exact lt_of_lt_of_le ht (sq_nonneg x)

/-- For `t ≥ 0`, the preimage of `Iic t` under squaring is `Icc (-√t) (√t)`. -/
lemma sq_preimage_Iic_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (fun x : ℝ => x ^ 2) ⁻¹' Set.Iic t = Set.Icc (-Real.sqrt t) (Real.sqrt t) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Icc]
  exact Real.sq_le ht

/-! ### Jacobian density identity -/

/-- **Jacobian identity**: for `u > 0`, the Gamma(1/2,1/2) density at `u²` times the Jacobian
`2u` equals twice the standard normal density at `u`.  This is the key algebraic step in the
change-of-variables argument `t = u²` that converts the Gamma CDF into the Gaussian CDF. -/
lemma jacobian_pdf_eq {u : ℝ} (hu : 0 < u) :
    gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) (u ^ 2) * (2 * u) = 2 * gaussianPDFReal 0 1 u := by
  have hu2nn : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
  simp only [gammaPDFReal, if_pos hu2nn, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Real.Gamma_one_half_eq,
      show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) from by norm_num,
      Real.rpow_neg hu2nn,
      show (u ^ 2) ^ ((1 : ℝ) / 2) = u from by
        rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_sq hu.le,
      show -(1 / 2 * u ^ 2) = -u ^ 2 / 2 from by ring]
  -- Goal: (1/2)^(1/2) / √π * u⁻¹ * exp(-u²/2) * (2*u) = 2 * (√(2π))⁻¹ * exp(-u²/2)
  -- Step 1: prove the constant factor equality  (1/2)^(1/2) / √π = (√(2π))⁻¹
  have hconst : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.sqrt Real.pi = (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← Real.sqrt_inv]
    congr 1
    field_simp [Real.pi_pos.ne']
  -- Step 2: rewrite using hconst and cancel u⁻¹ * u
  rw [hconst]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * u⁻¹ * Real.exp (-u ^ 2 / 2) * (2 * u)
      = (Real.sqrt (2 * Real.pi))⁻¹ * (u⁻¹ * u) * Real.exp (-u ^ 2 / 2) * 2 := by ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * 1 * Real.exp (-u ^ 2 / 2) * 2 := by
        rw [inv_mul_cancel₀ hu.ne']
    _ = 2 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-u ^ 2 / 2)) := by ring

/-! ### Helper lemmas for the change-of-variables proof -/

/-- The Gaussian density at `0` mean unit variance is symmetric: `g(-x) = g(x)`. -/
lemma gaussianPDFReal_zero_one_neg (x : ℝ) :
    gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, sub_zero]
  congr 2
  ring

/-- The standard normal pdf is continuous (derived from the explicit formula). -/
lemma continuous_gaussianPDFReal_zero_one : Continuous (gaussianPDFReal 0 1) := by
  unfold gaussianPDFReal
  refine continuous_const.mul ?_
  refine Real.continuous_exp.comp ?_
  refine Continuous.div_const ?_ _
  refine (Continuous.pow ?_ 2).neg
  exact (continuous_id'.sub continuous_const)

/-- For any `t : ℝ`, the Gaussian integral on `[-√t, √t]` is twice the integral on `[0, √t]`. -/
lemma gaussian_integral_symm (t : ℝ) :
    ∫ x in (-Real.sqrt t)..Real.sqrt t, gaussianPDFReal 0 1 x =
      2 * ∫ x in (0 : ℝ)..Real.sqrt t, gaussianPDFReal 0 1 x := by
  have hint_neg :
      (∫ x in (-Real.sqrt t)..(0 : ℝ), gaussianPDFReal 0 1 x) =
        ∫ x in (0 : ℝ)..Real.sqrt t, gaussianPDFReal 0 1 x := by
    have hcomp : (∫ x in (-Real.sqrt t)..(0 : ℝ),
            (fun y : ℝ => gaussianPDFReal 0 1 (-y)) (-x)) =
        ∫ x in (0 : ℝ)..Real.sqrt t, gaussianPDFReal 0 1 (-x) := by
      simp
    have h1 : (∫ x in (-Real.sqrt t)..(0 : ℝ), gaussianPDFReal 0 1 x) =
        ∫ x in (-Real.sqrt t)..(0 : ℝ),
          (fun y : ℝ => gaussianPDFReal 0 1 (-y)) (-x) := by
      apply intervalIntegral.integral_congr
      intro x _; simp
    rw [h1, hcomp]
    refine intervalIntegral.integral_congr ?_
    intro x _
    exact gaussianPDFReal_zero_one_neg x
  have hcont : Continuous (gaussianPDFReal 0 1) := continuous_gaussianPDFReal_zero_one
  have hii_neg : IntervalIntegrable (gaussianPDFReal 0 1) volume (-Real.sqrt t) 0 :=
    hcont.intervalIntegrable _ _
  have hii_pos : IntervalIntegrable (gaussianPDFReal 0 1) volume 0 (Real.sqrt t) :=
    hcont.intervalIntegrable _ _
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals (a := -Real.sqrt t) (b := 0)
      (c := Real.sqrt t) hii_neg hii_pos
  rw [← hsplit, hint_neg]
  ring

/-- Integrability of the gamma pdf on `Icc 0 t` follows from finite total lintegral. -/
lemma integrable_gammaPDFReal_on_Icc (t : ℝ) :
    IntegrableOn (gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ)) (Set.Icc (0 : ℝ) t) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hpdf_nn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) t)]
      gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) :=
    ae_of_all _ (gammaPDFReal_nonneg ha hr)
  have hmeas : AEStronglyMeasurable (gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ))
      (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    (stronglyMeasurable_gammaPDFReal _ _).aestronglyMeasurable
  rw [IntegrableOn, ← lintegral_ofReal_ne_top_iff_integrable hmeas hpdf_nn]
  -- The restricted lintegral is bounded by the total lintegral, which is 1.
  have hbound : (∫⁻ x in Set.Icc (0 : ℝ) t,
      ENNReal.ofReal (gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) x)) ≤
        ∫⁻ x, ENNReal.ofReal (gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) x) := by
    exact setLIntegral_le_lintegral _ _
  have htotal : ∫⁻ x, ENNReal.ofReal (gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) x) = 1 := by
    have := lintegral_gammaPDF_eq_one ha hr
    simpa [gammaPDF] using this
  rw [htotal] at hbound
  exact (lt_of_le_of_lt hbound ENNReal.one_lt_top).ne

/-- Core distributional identity: squaring a standard normal gives `χ²(1)`.
Proved via `Measure.ext_of_Iic` by matching CDFs.  For `t < 0` both CDFs are zero;
for `t ≥ 0` the Gaussian CDF on `Icc (-√t, √t)` equals the Gamma CDF on `[0,t]`
via the substitution `s = u²` and `jacobian_pdf_eq`. -/
theorem gaussianReal_map_sq_eq_chiSquared_one :
    (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) = chiSquared 1 := by
  -- The pushforward of a probability measure is a (finite) probability measure.
  haveI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun x : ℝ => x ^ 2)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_Iic
  intro t
  simp only [Measure.map_apply (by fun_prop : Measurable fun x : ℝ => x ^ 2) measurableSet_Iic]
  by_cases ht : t < 0
  · -- Case t < 0: preimage is empty and Gamma PDF integrates to 0
    rw [sq_preimage_Iic_of_neg ht, measure_empty]
    symm
    rw [chiSquared_one_eq, gammaMeasure, withDensity_apply _ measurableSet_Iic]
    exact le_antisymm
      ((lintegral_mono_set (Set.Iic_subset_Iio.mpr ht)).trans
        (lintegral_gammaPDF_of_nonpos le_rfl).le)
      (zero_le _)
  · -- Case t ≥ 0
    rw [not_lt] at ht
    rw [sq_preimage_Iic_of_nonneg ht]
    set s := Real.sqrt t with hs_def
    have hs_nn : 0 ≤ s := Real.sqrt_nonneg t
    have hs_sq : s ^ 2 = t := Real.sq_sqrt ht
    have ha : (0 : ℝ) < 1 / 2 := by norm_num
    have hr : (0 : ℝ) < 1 / 2 := by norm_num
    -- Step 1 (LHS): rewrite Gaussian measure on `Icc (-s) s`.
    have hLHS_eq : (gaussianReal 0 1) (Set.Icc (-s) s) =
        ENNReal.ofReal (2 * ∫ x in (0 : ℝ)..s, gaussianPDFReal 0 1 x) := by
      rw [gaussianReal_apply_eq_integral 0 (one_ne_zero) (Set.Icc (-s) s)]
      congr 1
      rw [show (∫ x in Set.Icc (-s) s, gaussianPDFReal 0 1 x) =
              ∫ x in (-s)..s, gaussianPDFReal 0 1 x from by
            rw [intervalIntegral.integral_of_le (by linarith : (-s) ≤ s),
                MeasureTheory.integral_Icc_eq_integral_Ioc]]
      exact gaussian_integral_symm t
    rw [hLHS_eq]
    -- Step 2 (RHS): chi-squared on `Iic t` via the gamma measure.
    rw [chiSquared_one_eq, gammaMeasure, withDensity_apply _ measurableSet_Iic]
    rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ ht,
        lintegral_gammaPDF_of_nonpos le_rfl, zero_add]
    -- Step 3 (RHS): convert lintegral on `Icc 0 t` to ofReal of Bochner integral.
    have hpdf_nn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) t)]
        gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) :=
      ae_of_all _ (gammaPDFReal_nonneg ha hr)
    have hint_gamma : IntegrableOn (gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ))
        (Set.Icc (0 : ℝ) t) := integrable_gammaPDFReal_on_Icc t
    have hRHS_to_real : (∫⁻ x in Set.Icc (0 : ℝ) t, gammaPDF (1 / 2 : ℝ) (1 / 2 : ℝ) x) =
        ENNReal.ofReal (∫ x in Set.Icc (0 : ℝ) t, gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) x) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint_gamma hpdf_nn]
      rfl
    rw [hRHS_to_real]
    -- Step 4 (RHS): set integral on `Icc 0 t` to interval integral `0..t`.
    have hRHS_int : (∫ x in Set.Icc (0 : ℝ) t, gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) x) =
        ∫ x in (0 : ℝ)..t, gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) x := by
      rw [intervalIntegral.integral_of_le ht, MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [hRHS_int]
    -- Step 5 (RHS): change of variables `x = u^2`, `dx = 2u du`, on `[0, √t]`.
    -- The change-of-variables theorem says
    --   ∫ u in 0..s, (g ∘ f) u * f' u = ∫ x in f 0 .. f s, g x
    -- With f = (·^2), f' = (2*·), g = gammaPDFReal(1/2)(1/2), f 0 = 0, f s = t.
    have hf_cont : ContinuousOn (fun x : ℝ => x ^ 2) (Set.uIcc (0 : ℝ) s) := by fun_prop
    have hff' : ∀ x ∈ Set.Ioo (min (0 : ℝ) s) (max (0 : ℝ) s),
        HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      intro x _
      have := (hasDerivAt_pow 2 x)
      simpa [pow_one, mul_comm] using this
    have hf'_nn : ∀ x ∈ Set.Ioo (min (0 : ℝ) s) (max (0 : ℝ) s), 0 ≤ 2 * x := by
      intro x hx
      have hxnn : 0 ≤ x := by
        have : (0 : ℝ) ≤ min 0 s := le_min le_rfl hs_nn
        exact this.trans hx.1.le
      linarith
    have hcov := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (g := gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ))
      (a := (0 : ℝ)) (b := s) hf_cont hff' hf'_nn
    -- After rewrite, we have:
    --   ∫ u in 0..s, gammaPDFReal(1/2)(1/2)(u^2) * (2*u) = ∫ x in 0..t, gammaPDFReal(1/2)(1/2) x
    have hcov' : (∫ u in (0 : ℝ)..s, gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) (u ^ 2) * (2 * u)) =
        ∫ x in (0 : ℝ)..t, gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) x := by
      have h0 : ((fun x : ℝ => x ^ 2) 0) = 0 := by norm_num
      have hs2 : ((fun x : ℝ => x ^ 2) s) = t := by simpa using hs_sq
      simpa [Function.comp, h0, hs2] using hcov
    rw [← hcov']
    -- Step 6: use `jacobian_pdf_eq` (equality holds for `u > 0`, hence ae).
    have hjac : (∫ u in (0 : ℝ)..s, gammaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) (u ^ 2) * (2 * u)) =
        ∫ u in (0 : ℝ)..s, 2 * gaussianPDFReal 0 1 u := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu_pos : 0 < u := by
        rw [Set.uIoc_of_le hs_nn] at hu
        exact hu.1
      exact jacobian_pdf_eq hu_pos
    rw [hjac]
    -- Step 7: pull out the constant factor `2`.
    rw [intervalIntegral.integral_const_mul]

theorem hasLaw_sq_chiSquared_one
    {Ω : Type*} [MeasureSpace Ω]
    {W : Ω → ℝ} (hLaw : HasLaw W (gaussianReal 0 1)) :
    HasLaw (fun ω => (W ω)^2) (chiSquared 1) := by
  exact HasLaw.comp ⟨by fun_prop, gaussianReal_map_sq_eq_chiSquared_one⟩ hLaw

/-! ### Gamma convolution lemma -/

/-- Pointwise additive convolution identity for two Gamma densities with the same rate.
This is the analytic core of Gamma additivity: it amounts to evaluating
`∫₀ˣ y^(a-1) (x-y)^(b-1) dy = x^(a+b-1) · B(a,b)` for `x > 0` and using the Beta identity
`B(a,b) = Γ(a)Γ(b)/Γ(a+b)`.

## Proof outline

For `x < 0`: the integrand `gammaPDF a r y * gammaPDF b r (-y + x)` is 0 a.e.  Need both
factors nonzero, i.e. `0 ≤ y` (from `gammaPDF_of_neg`) AND `0 ≤ -y + x` (i.e. `y ≤ x`).
For `x < 0` the conjunction is empty, so the lintegral is 0; and `gammaPDF (a+b) r x = 0`
by `gammaPDF_of_neg`.  Closed below.

For `x > 0` (the analytic core):
```
(gammaPDF a r ⋆ₗ gammaPDF b r) x
  = ∫⁻ y, gammaPDF a r y * gammaPDF b r (-y + x) ∂volume
  = ∫⁻ y in Ioo 0 x, ENNReal.ofReal (gammaPDFReal a r y * gammaPDFReal b r (x - y))
  = ENNReal.ofReal (∫ y in Ioo 0 x, gammaPDFReal a r y * gammaPDFReal b r (x - y))
```
Substitute `y = x · u`, `dy = x · du`, mapping `Ioo 0 x → Ioo 0 1`:
```
∫ y in (0, x), y^(a-1) (x-y)^(b-1) dy
  = x^(a-1) · x^(b-1) · x · ∫ u in (0, 1), u^(a-1) (1-u)^(b-1) du
  = x^(a+b-1) · B(a, b)
```
With `B(a, b) = Γ(a)·Γ(b)/Γ(a+b)` (the real Beta function `ProbabilityTheory.beta`):
```
∫ y in (0, x), gammaPDFReal a r y * gammaPDFReal b r (x - y)
  = r^(a+b)/(Γ(a)·Γ(b)) · exp(-r·x) · x^(a+b-1) · Γ(a)·Γ(b)/Γ(a+b)
  = r^(a+b)/Γ(a+b) · x^(a+b-1) · exp(-r·x)
  = gammaPDFReal (a+b) r x
```

## Mathlib API needed (and gaps discovered)

* `MeasureTheory.lconvolution_def` / unfold: `(f ⋆ₗ[μ] g) x = ∫⁻ y, f y * g (-y + x) ∂μ`
  (`Mathlib/Analysis/LConvolution.lean`).
* `ProbabilityTheory.beta α β := Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)` and
  `ProbabilityTheory.beta_eq_betaIntegralReal`
  (`Mathlib/Probability/Distributions/Beta.lean:33,41`) — real-valued Beta function.
* `Complex.betaIntegral` and `Complex.Gamma_mul_Gamma_eq_betaIntegral`
  (`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:60,126`) — complex only;
  real version must be obtained via `beta_eq_betaIntegralReal`.
* `ofReal_integral_eq_lintegral_ofReal` to swap a Bochner integral over real-valued
  nonnegative integrand with `ENNReal.ofReal` of an `lintegral`.
* `intervalIntegral.integral_comp_mul_left` for the substitution `y = x · u`.
* `gammaPDFReal_nonneg`, `gammaPDF_of_neg`, `gammaPDF_of_nonneg` (already in Mathlib).

## Concrete next tactic steps

1. Use `Filter.EventuallyEq.of_forall_eq_of_compl_measure_zero` (or `ae_iff`) to reduce
   to pointwise equality on `{x | x ≠ 0}` (`{0}` has volume zero).
2. Split on `x < 0` (closed below) vs `x > 0`.
3. For `x > 0`: unfold `lconvolution`, then `setLIntegral_congr_set` to reduce to
   `Ioo 0 x`, apply `ofReal_integral_eq_lintegral_ofReal`, use the substitution above
   to land at the Beta integral, lift to Complex via `Complex.ofReal_*`, apply
   `Gamma_mul_Gamma_eq_betaIntegral`, project back.
-/
private lemma gammaPDF_lconvolution_eq {a b r : ℝ} (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    (gammaPDF a r ⋆ₗ[volume] gammaPDF b r) =ᵐ[volume] gammaPDF (a + b) r := by
  -- Helper: pointwise vanishing of the convolution at any `x < 0`.
  have hLHS_neg : ∀ {x : ℝ}, x < 0 →
      (gammaPDF a r ⋆ₗ[volume] gammaPDF b r) x = 0 := by
    intro x hx
    -- Unfold the additive convolution: it is `∫⁻ y, gammaPDF a r y * gammaPDF b r (-y + x)`.
    rw [lconvolution_def]
    -- The integrand vanishes a.e. (in fact, pointwise everywhere).
    -- For nonzero, need `0 ≤ y` (so `gammaPDF a r y ≠ 0`) AND `0 ≤ -y + x` (i.e., `y ≤ x`).
    -- For `x < 0` the conjunction `0 ≤ y ≤ x` is empty.
    have hmeas : Measurable fun y : ℝ => gammaPDF a r y * gammaPDF b r (-y + x) := by
      have h1 : Measurable (gammaPDF a r) :=
        (measurable_gammaPDFReal a r).ennreal_ofReal
      have h2 : Measurable (gammaPDF b r) :=
        (measurable_gammaPDFReal b r).ennreal_ofReal
      exact h1.mul (h2.comp (measurable_id.neg.add_const x))
    refine (lintegral_eq_zero_iff hmeas).mpr ?_
    refine ae_of_all _ (fun y => ?_)
    simp only [Pi.zero_apply, mul_eq_zero]
    by_cases hy : 0 ≤ y
    · -- y ≥ 0: then -y + x < 0 since x < 0, so the second factor is 0.
      right
      apply gammaPDF_of_neg
      linarith
    · -- y < 0: the first factor is 0.
      left
      exact gammaPDF_of_neg (lt_of_not_ge hy)
  -- Helper: pointwise equality for `x > 0` (the analytic core).
  have hpos : ∀ {x : ℝ}, 0 < x →
      (gammaPDF a r ⋆ₗ[volume] gammaPDF b r) x = gammaPDF (a + b) r x := by
    intro x hx
    -- Abbreviations for positivity facts.
    have hΓa_pos : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
    have hΓb_pos : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
    have hΓab_pos : 0 < Real.Gamma (a + b) := Real.Gamma_pos_of_pos (add_pos ha hb)
    have hra_pos : 0 < r ^ a := Real.rpow_pos_of_pos hr a
    have hrb_pos : 0 < r ^ b := Real.rpow_pos_of_pos hr b
    have hab_pos : 0 < a + b := add_pos ha hb
    -- Step A: prove the residual real integral identity.
    -- ∫ y in 0..x, y^(a-1) * (x-y)^(b-1) = x^(a+b-1) * beta a b.
    have hbeta_real :
        ∫ y in (0:ℝ)..x, y ^ (a - 1) * (x - y) ^ (b - 1) =
          x ^ (a + b - 1) * ProbabilityTheory.beta a b := by
      -- Use the complex version `Complex.betaIntegral_scaled` and lift via ofReal.
      have hC :
          ∫ y in (0:ℝ)..x, ((y : ℂ) ^ ((a : ℂ) - 1) * (((x : ℂ) - (y : ℂ)) ^ ((b : ℂ) - 1))) =
            ((x : ℂ)) ^ ((a : ℂ) + (b : ℂ) - 1) * Complex.betaIntegral a b :=
        Complex.betaIntegral_scaled (a : ℂ) (b : ℂ) hx
      -- Identify the complex integrand on (0, x) with ofReal of the real integrand.
      have hreal_to_complex :
          ∫ y in (0:ℝ)..x, ((y : ℂ) ^ ((a : ℂ) - 1) * (((x : ℂ) - (y : ℂ)) ^ ((b : ℂ) - 1))) =
            ((∫ y in (0:ℝ)..x, y ^ (a - 1) * (x - y) ^ (b - 1) : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]
        refine intervalIntegral.integral_congr_ae ?_
        refine ae_of_all _ (fun y hy => ?_)
        rw [Set.uIoc_of_le hx.le] at hy
        have hy0 : 0 ≤ y := hy.1.le
        have hxy : 0 ≤ x - y := by linarith [hy.2]
        have hxy_eq : ((x : ℂ) - (y : ℂ)) = (((x - y : ℝ)) : ℂ) := by push_cast; ring
        rw [hxy_eq]
        have ha1 : ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) := by push_cast; ring
        have hb1 : ((b : ℂ) - 1) = ((b - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [ha1, hb1, ← Complex.ofReal_cpow hy0, ← Complex.ofReal_cpow hxy,
          ← Complex.ofReal_mul]
      rw [hreal_to_complex] at hC
      -- Identify ((x : ℂ))^((a+b-1 : ℝ) : ℂ) with ofReal of x^(a+b-1).
      have hxc : ((x : ℂ)) ^ ((a : ℂ) + (b : ℂ) - 1) = (((x ^ (a + b - 1) : ℝ)) : ℂ) := by
        have heq : ((a : ℂ) + (b : ℂ) - 1) = ((a + b - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [heq, ← Complex.ofReal_cpow hx.le]
      rw [hxc] at hC
      -- Identify Complex.betaIntegral a b with ofReal of beta a b via Gamma identity.
      have hbeta_id : Complex.betaIntegral (a : ℂ) (b : ℂ) =
          (((ProbabilityTheory.beta a b) : ℝ) : ℂ) := by
        have hbg : Complex.betaIntegral (a : ℂ) (b : ℂ) =
            Complex.Gamma a * Complex.Gamma b / Complex.Gamma ((a : ℂ) + (b : ℂ)) := by
          rw [Complex.betaIntegral_eq_Gamma_mul_div]
          all_goals simp [ha, hb]
        rw [hbg]
        have hsum : ((a : ℂ) + (b : ℂ)) = ((a + b : ℝ) : ℂ) := by push_cast; ring
        rw [hsum, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
        rw [ProbabilityTheory.beta]
        push_cast; ring
      rw [hbeta_id] at hC
      -- Now hC : ofReal LHS = ofReal RHS_const * ofReal RHS_beta. Combine and use injectivity.
      rw [← Complex.ofReal_mul] at hC
      exact Complex.ofReal_injective hC
    -- Step B: prove integrability of the polynomial integrand on Ioo 0 x.
    -- Split at x/2: on [0, x/2], use rpow integrability of y^(a-1) and continuity of (x-y)^(b-1).
    -- On [x/2, x], symmetric (use rpow integrability of (x-y)^(b-1) via change of variable).
    have hpoly_int : IntegrableOn
        (fun y => y ^ (a - 1) * (x - y) ^ (b - 1)) (Set.Ioo 0 x) volume := by
      have hxh_pos : 0 < x / 2 := by linarith
      have hxh_lt : x / 2 < x := by linarith
      -- Integrability on [0, x/2]: y^(a-1) integrable; (x-y)^(b-1) continuous on [0, x/2].
      have hII_left : IntervalIntegrable
          (fun y : ℝ => y ^ (a - 1) * (x - y) ^ (b - 1)) volume 0 (x / 2) := by
        apply IntervalIntegrable.mul_continuousOn
        · exact intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a - 1)
        · -- (x - y)^(b-1) is continuous on [0, x/2] because x - y > 0 there.
          apply ContinuousOn.rpow_const
          · fun_prop
          · intro y hy
            rw [Set.uIcc_of_le hxh_pos.le] at hy
            left
            linarith [hy.2]
      -- Integrability on [x/2, x]: change of variable z = x - y reduces to rpow on [0, x/2].
      have hII_right : IntervalIntegrable
          (fun y : ℝ => y ^ (a - 1) * (x - y) ^ (b - 1)) volume (x / 2) x := by
        have hII_sym : IntervalIntegrable
            (fun z : ℝ => (x - z) ^ (a - 1) * z ^ (b - 1)) volume 0 (x / 2) := by
          apply IntervalIntegrable.continuousOn_mul
            (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < b - 1))
          · apply ContinuousOn.rpow_const
            · fun_prop
            · intro z hz
              rw [Set.uIcc_of_le hxh_pos.le] at hz
              left; linarith [hz.2]
        -- Apply comp_sub_left with c = x: gives integrability of (fun y => f(x - y)) on (x, x/2).
        have key := hII_sym.comp_sub_left x
        -- key : IntervalIntegrable (fun y => (x - (x-y))^(a-1) * (x-y)^(b-1)) volume (x-0) (x-x/2)
        -- The function (x - (x-y))^(a-1) * (x-y)^(b-1) = y^(a-1) * (x-y)^(b-1).
        have hfun_eq :
            (fun y : ℝ => (x - (x - y)) ^ (a - 1) * (x - y) ^ (b - 1)) =
            (fun y : ℝ => y ^ (a - 1) * (x - y) ^ (b - 1)) := by
          funext y
          have : x - (x - y) = y := by ring
          rw [this]
        rw [hfun_eq] at key
        -- key : IntervalIntegrable ... volume (x - 0) (x - x/2) = (x, x/2)
        -- IntervalIntegrable is symmetric in endpoints.
        have hxsub : x - 0 = x := by ring
        have hxsub2 : x - x / 2 = x / 2 := by ring
        rw [hxsub, hxsub2] at key
        exact key.symm
      -- Combine the two IntervalIntegrable pieces.
      have hII : IntervalIntegrable
          (fun y : ℝ => y ^ (a - 1) * (x - y) ^ (b - 1)) volume 0 x :=
        hII_left.trans hII_right
      -- Convert IntervalIntegrable on [0, x] to IntegrableOn (Ioo 0 x).
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le] at hII
      exact hII.mono_set Set.Ioo_subset_Ioc_self
    -- Step 1: unfold lconvolution and reduce to support Ioo 0 x.
    rw [lconvolution_def]
    -- The integrand vanishes a.e. outside Ioo 0 x (pointwise on `Iio 0 ∪ Ioi x`,
    -- and the boundary `{0, x}` has measure zero).
    have hint_restrict :
        ∫⁻ y, gammaPDF a r y * gammaPDF b r (-y + x) =
          ∫⁻ y in Set.Ioo 0 x, gammaPDF a r y * gammaPDF b r (-y + x) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr_ae
      have hboundary_null : (volume : Measure ℝ) ({(0 : ℝ), x} : Set ℝ) = 0 := by
        rw [show (({(0 : ℝ), x} : Set ℝ)) = {(0:ℝ)} ∪ {x} from rfl]
        exact measure_union_null (measure_singleton 0) (measure_singleton x)
      have h_outside : ∀ y, y ∉ ({(0 : ℝ), x} : Set ℝ) → y ∉ Set.Ioo 0 x →
          gammaPDF a r y * gammaPDF b r (-y + x) = 0 := by
        intro y hne hyout
        have hne0 : y ≠ 0 := fun h => hne (by simp [h])
        have hnex : y ≠ x := fun h => hne (by simp [h])
        rcases lt_or_ge y 0 with hlt | hge
        · rw [gammaPDF_of_neg hlt]; ring
        · rcases eq_or_lt_of_le hge with hzeroy | hpos
          · exact absurd hzeroy.symm hne0
          · -- y > 0; since y ∉ Ioo 0 x and y ≠ x, must have y > x.
            have hxy : x < y := by
              by_contra hc
              push Not at hc
              rcases eq_or_lt_of_le hc with hyx | hyltx
              · exact hnex hyx
              · exact hyout ⟨hpos, hyltx⟩
            have hneg : -y + x < 0 := by linarith
            rw [gammaPDF_of_neg hneg]; ring
      have hae : ∀ᵐ y ∂volume, y ∉ ({(0 : ℝ), x} : Set ℝ) := by
        rw [ae_iff]
        simp only [not_not]
        exact hboundary_null
      filter_upwards [hae] with y hyc
      by_cases hy : y ∈ Set.Ioo 0 x
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, h_outside y hyc hy]
    rw [hint_restrict]
    -- Step 2: identify integrand with ofReal of nonneg.
    have hpdf_eq_pos : ∀ y ∈ Set.Ioo 0 x,
        gammaPDF a r y * gammaPDF b r (-y + x) =
          ENNReal.ofReal (gammaPDFReal a r y * gammaPDFReal b r (-y + x)) := by
      intro _ _
      simp only [gammaPDF]
      rw [← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr _)]
    rw [setLIntegral_congr_fun measurableSet_Ioo hpdf_eq_pos]
    -- Step 3: identify the integrand on Ioo 0 x with constant * polynomial.
    have hsimp_integrand : ∀ y ∈ Set.Ioo 0 x,
        gammaPDFReal a r y * gammaPDFReal b r (-y + x) =
          (r ^ a / Real.Gamma a * (r ^ b / Real.Gamma b) * Real.exp (-(r * x))) *
            (y ^ (a - 1) * (x - y) ^ (b - 1)) := by
      intro y hy
      have hy_pos : 0 < y := hy.1
      have hxy_pos' : 0 < -y + x := by linarith [hy.2]
      simp only [gammaPDFReal, if_pos hy_pos.le, if_pos hxy_pos'.le]
      have hsub_eq : (-y + x) ^ (b - 1) = (x - y) ^ (b - 1) := by
        congr 1; ring
      rw [hsub_eq]
      calc r ^ a / Real.Gamma a * y ^ (a - 1) * Real.exp (-(r * y)) *
            (r ^ b / Real.Gamma b * (x - y) ^ (b - 1) * Real.exp (-(r * (-y + x))))
          = r ^ a / Real.Gamma a * (r ^ b / Real.Gamma b) *
            (y ^ (a - 1) * (x - y) ^ (b - 1)) *
            (Real.exp (-(r * y)) * Real.exp (-(r * (-y + x)))) := by ring
        _ = r ^ a / Real.Gamma a * (r ^ b / Real.Gamma b) *
            (y ^ (a - 1) * (x - y) ^ (b - 1)) * Real.exp (-(r * x)) := by
              rw [← Real.exp_add]; congr 1; ring
        _ = r ^ a / Real.Gamma a * (r ^ b / Real.Gamma b) * Real.exp (-(r * x)) *
            (y ^ (a - 1) * (x - y) ^ (b - 1)) := by ring
    -- Step 4: conclude via constant pull-out.
    -- Integrability follows from hpoly_int.
    have hint_real_int : Integrable
        (fun y => gammaPDFReal a r y * gammaPDFReal b r (-y + x))
        (volume.restrict (Set.Ioo 0 x)) := by
      have hC_int : Integrable
          (fun y => (r ^ a / Real.Gamma a * (r ^ b / Real.Gamma b) * Real.exp (-(r * x))) *
            (y ^ (a - 1) * (x - y) ^ (b - 1)))
          (volume.restrict (Set.Ioo 0 x)) := hpoly_int.const_mul _
      apply hC_int.congr
      refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
      exact ae_of_all _ (fun y hy => (hsimp_integrand y hy).symm)
    have hint_real_ae_nn : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 x)]
        fun y => gammaPDFReal a r y * gammaPDFReal b r (-y + x) :=
      ae_of_all _ (fun y => mul_nonneg (gammaPDFReal_nonneg ha hr _)
        (gammaPDFReal_nonneg hb hr _))
    rw [← ofReal_integral_eq_lintegral_ofReal hint_real_int hint_real_ae_nn]
    -- Pull out constant from Bochner integral.
    have hint_split :
        ∫ y in Set.Ioo 0 x, gammaPDFReal a r y * gammaPDFReal b r (-y + x) =
          (r ^ a / Real.Gamma a * (r ^ b / Real.Gamma b) * Real.exp (-(r * x))) *
            ∫ y in Set.Ioo 0 x, y ^ (a - 1) * (x - y) ^ (b - 1) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      exact hsimp_integrand
    rw [hint_split]
    -- Convert ∫ in Ioo 0 x = ∫ in 0..x.
    have hIoo_to_intervalIntegral :
        ∫ y in Set.Ioo 0 x, y ^ (a - 1) * (x - y) ^ (b - 1) =
          ∫ y in (0:ℝ)..x, y ^ (a - 1) * (x - y) ^ (b - 1) := by
      rw [intervalIntegral.integral_of_le hx.le, ← integral_Ioc_eq_integral_Ioo]
    rw [hIoo_to_intervalIntegral, hbeta_real]
    -- Final algebra: ofReal (Cab_const * x^(a+b-1) * beta a b) = gammaPDF (a+b) r x.
    rw [gammaPDF_of_nonneg hx.le]
    congr 1
    rw [ProbabilityTheory.beta, Real.rpow_add hr a b]
    field_simp
  -- Combine: equality holds for all `x ≠ 0`, and `{0}` has volume zero.
  rw [Filter.EventuallyEq, ae_iff]
  -- Goal: volume {x | ¬ (LHS x = RHS x)} = 0.
  -- The disagreement set is contained in `{0}` (a measure-zero set).
  refine measure_mono_null (t := ({(0 : ℝ)} : Set ℝ)) ?_ (measure_singleton _)
  intro x hx_neq
  -- We must show `x ∈ {0}`.  By trichotomy: `x < 0`, `x = 0`, or `x > 0`.
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · exact absurd ((hLHS_neg hlt).trans (gammaPDF_of_neg hlt).symm) hx_neq
  · exact heq
  · exact absurd (hpos hgt) hx_neq

/-- **Gamma additivity**: the additive convolution of two Gamma measures with the same rate
parameter is again a Gamma measure: `Gamma(a, r) ∗ Gamma(b, r) = Gamma(a+b, r)`.  This
corresponds to the fact that the sum of independent Gamma(a, r) and Gamma(b, r) random
variables is Gamma(a+b, r).

The proof reduces to the pointwise identity `gammaPDF_lconvolution_eq` (the additive
convolution of two Gamma densities equals the sum-rate Gamma density a.e.) via the
identity `withDensity f ∗ withDensity g = withDensity (f ⋆ₗ g)`. -/
lemma gammaMeasure_conv_same_rate_eq {a b r : ℝ} (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    gammaMeasure a r ∗ gammaMeasure b r = gammaMeasure (a + b) r := by
  have hmeas : ∀ a r : ℝ, Measurable (gammaPDF a r) := fun a r => by
    unfold gammaPDF
    exact (measurable_gammaPDFReal a r).ennreal_ofReal
  unfold gammaMeasure
  rw [conv_withDensity_eq_lconvolution (hmeas a r) (hmeas b r)]
  exact withDensity_congr_ae (gammaPDF_lconvolution_eq hr ha hb)

theorem hasLaw_add_chiSquared
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {Ω : Type*} [MeasureSpace Ω]
    {X Y : Ω → ℝ}
    (hX : HasLaw X (chiSquared a)) (hY : HasLaw Y (chiSquared b))
    (hIndep : IndepFun X Y) :
    HasLaw (fun ω => X ω + Y ω) (chiSquared (a + b)) := by
  have ha' : (0 : ℝ) < (a : ℝ) / 2 := div_pos (Nat.cast_pos.mpr ha) (by norm_num)
  have hb' : (0 : ℝ) < (b : ℝ) / 2 := div_pos (Nat.cast_pos.mpr hb) (by norm_num)
  haveI : IsProbabilityMeasure (chiSquared a) := isProbabilityMeasure_chiSquared ha
  haveI : IsProbabilityMeasure (chiSquared b) := isProbabilityMeasure_chiSquared hb
  have hsum := IndepFun.hasLaw_fun_add hX hY hIndep
  rw [chiSquared_eq a, chiSquared_eq b] at hsum
  -- The additive-convolution identity for gamma measures with the same rate.
  have hconv : gammaMeasure ((a:ℝ)/2) (1/2) ∗ gammaMeasure ((b:ℝ)/2) (1/2)
      = gammaMeasure (((a:ℝ)/2) + ((b:ℝ)/2)) (1/2) :=
    gammaMeasure_conv_same_rate_eq (by norm_num : (0:ℝ) < 1/2) ha' hb'
  rw [hconv] at hsum
  have hcast : ((a : ℝ) / 2 + (b : ℝ) / 2) = ((a + b : ℕ) : ℝ) / 2 := by
    push_cast; ring
  rw [hcast] at hsum
  rw [chiSquared_eq (a + b)]
  exact hsum

theorem hasLaw_sum_sq_chiSquared
    {k : ℕ} (hk : 0 < k)
    {Ω : Type*} [MeasureSpace Ω]
    {W : Fin k → Ω → ℝ}
    (hLaw : ∀ i, HasLaw (W i) (gaussianReal 0 1))
    (hIndep : ProbabilityTheory.iIndepFun W) :
    HasLaw (fun ω => ∑ i, (W i ω)^2) (chiSquared k) := by
  -- Reduce `k` to `n + 1` so we can induct on `n`.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  clear hk
  induction n with
  | zero =>
    -- Base case k = 1: a single squared standard normal is χ²(1).
    have hsum_eq : (fun ω => ∑ i : Fin 1, (W i ω)^2) = (fun ω => (W 0 ω)^2) := by
      funext ω
      simp
    rw [hsum_eq]
    exact hasLaw_sq_chiSquared_one (hLaw 0)
  | succ n ih =>
    -- Inductive step: the family has length `n + 2 = (n + 1) + 1`.
    -- Define the truncated family on the first `n + 1` indices.
    set V : Fin (n + 1) → Ω → ℝ := fun i => W i.castSucc with hV_def
    have hLawV : ∀ i, HasLaw (V i) (gaussianReal 0 1) := fun i => hLaw i.castSucc
    have hIndepV : ProbabilityTheory.iIndepFun V :=
      hIndep.precomp (Fin.castSucc_injective (n + 1))
    -- Apply the inductive hypothesis to V.
    have hIH : HasLaw (fun ω => ∑ i : Fin (n + 1), (V i ω)^2) (chiSquared (n + 1)) :=
      ih hLawV hIndepV
    -- The last squared standard normal has law χ²(1).
    have hLast : HasLaw (fun ω => (W (Fin.last (n + 1)) ω)^2) (chiSquared 1) :=
      hasLaw_sq_chiSquared_one (hLaw (Fin.last (n + 1)))
    -- Build independence between the partial sum (squared) and the last squared element.
    -- Step A: lift squaring through the iIndepFun structure.
    have hSqIndep : ProbabilityTheory.iIndepFun (fun i (ω : Ω) => (W i ω)^2) := by
      have hsq : Measurable (fun x : ℝ => x^2) := by fun_prop
      exact hIndep.comp (fun _ x => x^2) (fun _ => hsq)
    -- Step B: apply the additive sibling of `iIndepFun.indepFun_finset_prod_of_notMem`.
    let s : Finset (Fin (n + 2)) := (Finset.univ : Finset (Fin (n + 2))).erase (Fin.last (n + 1))
    have hLastNotMem : Fin.last (n + 1) ∉ s := Finset.notMem_erase _ _
    -- Use the AEMeasurable variant of the finset-sum lemma so we don't need Measurable.
    have hSqAEMeas : ∀ i, AEMeasurable (fun ω : Ω => (W i ω)^2) := by
      intro i
      have hWmeas : AEMeasurable (W i) := (hLaw i).aemeasurable
      exact hWmeas.pow_const 2
    have hIndepSumLast : ProbabilityTheory.IndepFun
        (∑ j ∈ s, fun ω : Ω => (W j ω)^2)
        (fun ω : Ω => (W (Fin.last (n + 1)) ω)^2) := by
      have := hSqIndep.indepFun_finset_sum_of_notMem₀ hSqAEMeas hLastNotMem
      exact this
    -- Step C: rewrite the finset sum as the `Fin (n+1)` sum via `Fin.castSucc`.
    have hsumRewrite : ∀ ω, ∑ j ∈ s, (W j ω)^2 = ∑ i : Fin (n + 1), (V i ω)^2 := by
      intro ω
      have hs_image : s = (Finset.univ : Finset (Fin (n + 1))).image Fin.castSucc := by
        ext j
        simp only [s, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
          Finset.mem_image]
        refine ⟨fun hj => ?_, fun ⟨i, hi⟩ => ?_⟩
        · -- j ≠ last → j is in the image of castSucc
          rcases Fin.eq_castSucc_or_eq_last j with hcs | hlast
          · obtain ⟨i, rfl⟩ := hcs
            exact ⟨i, rfl⟩
          · exact absurd hlast hj
        · subst hi
          exact (Fin.castSucc_lt_last i).ne
      rw [hs_image, Finset.sum_image
        ((Fin.castSucc_injective (n + 1)).injOn)]
    have hIndepFinal : ProbabilityTheory.IndepFun
        (fun ω => ∑ i : Fin (n + 1), (V i ω)^2)
        (fun ω => (W (Fin.last (n + 1)) ω)^2) := by
      have hfun_eq : (∑ j ∈ s, fun ω : Ω => (W j ω)^2) =
          (fun ω => ∑ i : Fin (n + 1), (V i ω)^2) := by
        funext ω
        rw [Finset.sum_apply]
        exact hsumRewrite ω
      rw [← hfun_eq]
      exact hIndepSumLast
    -- Apply the gamma-additivity result to conclude.
    have hAdd := hasLaw_add_chiSquared (a := n + 1) (b := 1)
      (Nat.succ_pos n) Nat.one_pos hIH hLast hIndepFinal
    -- Rewrite the goal so it matches `(fun ω => partial + last)`.
    have hgoal_eq : (fun ω => ∑ i : Fin (n + 2), (W i ω)^2) =
        (fun ω => (∑ i : Fin (n + 1), (V i ω)^2) + (W (Fin.last (n + 1)) ω)^2) := by
      funext ω
      simp [Fin.sum_univ_castSucc, V]
    rw [hgoal_eq]
    exact hAdd

/-- Finite-type version of `hasLaw_sum_sq_chiSquared`, obtained by reindexing along a bijection with
`Fin (card ι)`. This is convenient when the standard-normal coordinates are naturally indexed by a
finite subtype rather than by `Fin k`. -/
theorem hasLaw_sum_sq_chiSquared_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hk : 0 < Fintype.card ι)
    {Ω : Type*} [MeasureSpace Ω]
    {W : ι → Ω → ℝ}
    (hLaw : ∀ i, HasLaw (W i) (gaussianReal 0 1))
    (hIndep : ProbabilityTheory.iIndepFun W) :
    HasLaw (fun ω => ∑ i, (W i ω)^2) (chiSquared (Fintype.card ι)) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hLawFin : ∀ i : Fin (Fintype.card ι), HasLaw (W (e i)) (gaussianReal 0 1) :=
    fun i => hLaw (e i)
  have hIndepFin : ProbabilityTheory.iIndepFun (fun i : Fin (Fintype.card ι) => W (e i)) := by
    exact hIndep.precomp e.injective
  have hFin : HasLaw
      (fun ω => ∑ i : Fin (Fintype.card ι), (W (e i) ω)^2)
      (chiSquared (Fintype.card ι)) :=
    hasLaw_sum_sq_chiSquared hk hLawFin hIndepFin
  refine hFin.congr ?_
  filter_upwards with ω
  symm
  exact Fintype.sum_equiv e
    (fun i : Fin (Fintype.card ι) => (W (e i) ω)^2)
    (fun i : ι => (W i ω)^2)
    fun i => rfl

/-! ### Chi-squared distribution of quadratic forms with symmetric idempotent matrices -/

section QuadraticFormChiSquared

open Matrix

/-- Spectral expansion of the quadratic form `z ⬝ᵥ M *ᵥ z` in the eigenbasis of a
Hermitian real matrix: it equals the sum of eigenvalues times squared basis coordinates. -/
lemma quadForm_eq_sum_eigenvalues
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hH : M.IsHermitian)
    (z : EuclideanSpace ℝ (Fin n)) :
    (z : Fin n → ℝ) ⬝ᵥ (M *ᵥ (z : Fin n → ℝ))
      = ∑ i, hH.eigenvalues i * (hH.eigenvectorBasis.repr z i) ^ 2 := by
  set b := hH.eigenvectorBasis with hb_def
  -- Write (z : Fin n → ℝ) as a sum in the eigenbasis.
  have hz_coord : (z : Fin n → ℝ) = ∑ i, b.repr z i • ((b i : Fin n → ℝ)) := by
    have hsum : z = ∑ i, b.repr z i • b i := (b.sum_repr z).symm
    have : ((z : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
        = (((∑ i, b.repr z i • b i) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) :=
      congrArg _ hsum
    rw [this, WithLp.ofLp_sum]
    rfl
  -- Apply M to that sum; linearity + eigenvector identity.
  have hMz_coord : M *ᵥ (z : Fin n → ℝ)
      = ∑ i, (b.repr z i * hH.eigenvalues i) • ((b i : Fin n → ℝ)) := by
    rw [hz_coord, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mulVec_smul, hH.mulVec_eigenvectorBasis, smul_smul]
  -- Orthonormality of the eigenbasis as `Fin n → ℝ` vectors.  For real scalars the inner
  -- product coincides with the (flipped) dot product: ⟪x, y⟫_ℝ = y ⬝ᵥ x.
  have hinner_eq_dot : ∀ x y : EuclideanSpace ℝ (Fin n),
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ x y = ((y : Fin n → ℝ)) ⬝ᵥ ((x : Fin n → ℝ)) :=
    fun _ _ => rfl
  have horth : ∀ i j : Fin n,
      ((b i : Fin n → ℝ)) ⬝ᵥ ((b j : Fin n → ℝ)) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [dotProduct_comm, ← hinner_eq_dot]
    have := (orthonormal_iff_ite.mp b.orthonormal) i j
    simpa using this
  -- Expand the dot product step by step.
  rw [hMz_coord, hz_coord, sum_dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_dotProduct, dotProduct_sum, smul_eq_mul]
  have step : ∀ j, (b i : Fin n → ℝ) ⬝ᵥ ((b.repr z j * hH.eigenvalues j) • (b j : Fin n → ℝ))
      = (b.repr z j * hH.eigenvalues j) * (if i = j then (1 : ℝ) else 0) := by
    intro j; rw [dotProduct_smul, horth, smul_eq_mul]
  simp_rw [step]
  rw [Finset.sum_congr rfl (fun j _ => show
    (b.repr z j * hH.eigenvalues j) * (if i = j then (1 : ℝ) else 0)
      = if i = j then b.repr z i * hH.eigenvalues i else 0 by
    split_ifs with hij
    · rw [hij]; ring
    · ring)]
  rw [Finset.sum_ite_eq Finset.univ i]
  simp
  ring

/-- For a Hermitian idempotent real matrix, the number of indices whose eigenvalue is `1`
equals the rank of the matrix. -/
lemma card_eigenvalue_one_eq_rank_of_isHermitian_idempotent
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hH : M.IsHermitian) (hI : IsIdempotentElem M) :
    (Finset.univ.filter (fun i : Fin n => hH.eigenvalues i = 1)).card = M.rank := by
  -- Eigenvalues of a Hermitian idempotent real matrix are 0 or 1.
  have heig : ∀ i : Fin n, hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := fun i => by
    have hmem := hI.spectrum_subset ℝ (hH.eigenvalues_mem_spectrum_real i)
    simpa using hmem
  -- So the "= 1" predicate coincides with the "≠ 0" predicate.
  have hfilter_eq : Finset.univ.filter (fun i : Fin n => hH.eigenvalues i = 1)
      = Finset.univ.filter (fun i : Fin n => hH.eigenvalues i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rw [h]; norm_num
    · exact (heig i).resolve_left
  rw [hfilter_eq, hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]

/-- The coordinates of a standard Gaussian vector in an orthonormal basis are i.i.d. standard
normal. -/
lemma hasLaw_coords_of_stdGaussian
    {n : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis (Fin n) ℝ E)
    {Z : Ω → E} (hZ : HasLaw Z (stdGaussian E)) :
    (∀ i, HasLaw (fun ω => b.repr (Z ω) i) (gaussianReal 0 1)) ∧
      iIndepFun (fun i ω => b.repr (Z ω) i) := by
  -- Package `b.repr` as a HasLaw via Mathlib's `stdGaussian_map`.
  have hRepr : HasLaw (fun x : E => (b.repr x : EuclideanSpace ℝ (Fin n)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (stdGaussian E) :=
    ⟨b.repr.continuous.aemeasurable, stdGaussian_map b.repr⟩
  have hbZ : HasLaw (fun ω => b.repr (Z ω)) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    hRepr.comp hZ
  -- Bridge from `stdGaussian` on `EuclideanSpace` to `Measure.pi (fun _ => gaussianReal 0 1)`
  -- via the `ofLp` coercion (inverse of `toLp 2`).
  have hm_of : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by fun_prop
  have hm_to : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by fun_prop
  have hOfLp_map : (stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
    rw [← map_pi_eq_stdGaussian (ι := Fin n), Measure.map_map hm_of hm_to]
    simp [Function.comp_def]
  have hOfLp : HasLaw (fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨hm_of.aemeasurable, hOfLp_map⟩
  have hbZ_coord : HasLaw (fun ω => ((b.repr (Z ω)) : Fin n → ℝ))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    hOfLp.comp hbZ
  -- Per-coordinate laws via projection through the product measure.
  have hLaw : ∀ i : Fin n, HasLaw (fun ω => b.repr (Z ω) i) (gaussianReal 0 1) := by
    intro i
    refine ⟨hbZ_coord.aemeasurable.eval i, ?_⟩
    have h1 : (volume : Measure Ω).map (fun ω => b.repr (Z ω) i)
        = ((volume : Measure Ω).map (fun ω => ((b.repr (Z ω)) : Fin n → ℝ))).map
            (fun f : Fin n → ℝ => f i) := by
      rw [AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply i).aemeasurable
        hbZ_coord.aemeasurable]
      rfl
    rw [h1, hbZ_coord.map_eq]
    exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq
  -- Independence via the product-measure characterization.
  refine ⟨hLaw, ?_⟩
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hLaw i).aemeasurable)]
  rw [show (fun (ω : Ω) (i : Fin n) => b.repr (Z ω) i)
      = (fun ω => ((b.repr (Z ω)) : Fin n → ℝ)) from rfl]
  rw [hbZ_coord.map_eq]
  congr 1
  funext i
  exact ((hLaw i).map_eq).symm

/-- **Quadratic-form chi-squared theorem.** If `Z` is a standard Gaussian vector in
`EuclideanSpace ℝ (Fin n)` and `M` is a symmetric idempotent real `n × n` matrix of rank `r > 0`,
then the quadratic form `Z ⬝ᵥ M *ᵥ Z` has a chi-squared distribution with `r` degrees of freedom.

This is the key distributional fact underlying the finite-sample theory of least-squares variance
estimation in the homoskedastic normal regression model (Hansen, Chapter 5). -/
theorem hasLaw_quadForm_symmIdem_chiSquared
    {n : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {Z : Ω → EuclideanSpace ℝ (Fin n)}
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin n))))
    (hH : M.IsHermitian) (hI : IsIdempotentElem M) (hr : 0 < M.rank) :
    HasLaw (fun ω => (Z ω : Fin n → ℝ) ⬝ᵥ (M *ᵥ (Z ω : Fin n → ℝ))) (chiSquared M.rank) := by
  -- Step A: eigenbasis coordinates are iid N(0,1).
  obtain ⟨hLaw, hIndep⟩ := hasLaw_coords_of_stdGaussian hH.eigenvectorBasis hZ
  set b := hH.eigenvectorBasis with hb_def
  -- Step B: spectral expansion of the quadratic form.
  have hQF : ∀ ω, (Z ω : Fin n → ℝ) ⬝ᵥ (M *ᵥ (Z ω : Fin n → ℝ))
      = ∑ i, hH.eigenvalues i * (b.repr (Z ω) i) ^ 2 :=
    fun ω => quadForm_eq_sum_eigenvalues hH (Z ω)
  -- Step C: eigenvalues are 0 or 1; collapse to a sum over `S = {i : λᵢ = 1}`.
  have heig : ∀ i : Fin n, hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := fun i => by
    simpa using hI.spectrum_subset ℝ (hH.eigenvalues_mem_spectrum_real i)
  set S : Finset (Fin n) := Finset.univ.filter (fun i => hH.eigenvalues i = 1) with hS_def
  have hS_card : S.card = M.rank :=
    card_eigenvalue_one_eq_rank_of_isHermitian_idempotent hH hI
  have hQF' : ∀ ω, (Z ω : Fin n → ℝ) ⬝ᵥ (M *ᵥ (Z ω : Fin n → ℝ))
      = ∑ i ∈ S, (b.repr (Z ω) i) ^ 2 := by
    intro ω
    rw [hQF ω]
    have htransform : (∑ i, hH.eigenvalues i * (b.repr (Z ω) i) ^ 2)
        = ∑ i, if hH.eigenvalues i = 1 then (b.repr (Z ω) i) ^ 2 else 0 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases heig i with h0 | h1
      · rw [h0, if_neg (by norm_num : (0 : ℝ) ≠ 1)]; ring
      · rw [h1, if_pos rfl]; ring
    rw [htransform, ← Finset.sum_filter]
  -- Step D: reindex `S` by `Fin M.rank`, inherit iid N(0,1) on the subfamily.
  let eqn : Fin M.rank ≃ { x // x ∈ S } :=
    (finCongr hS_card.symm).trans S.equivFin.symm
  let σ : Fin M.rank → Fin n := fun i => (eqn i).val
  have hσ_inj : Function.Injective σ := fun i j h =>
    eqn.injective (Subtype.ext h)
  let W : Fin M.rank → Ω → ℝ := fun i ω => b.repr (Z ω) (σ i)
  have hLawW : ∀ i, HasLaw (W i) (gaussianReal 0 1) := fun i => hLaw (σ i)
  have hIndepW : iIndepFun W := hIndep.precomp hσ_inj
  -- Step E: rewrite the target sum via the reindexing, then apply `hasLaw_sum_sq_chiSquared`.
  have hSumReindex : ∀ ω, ∑ i ∈ S, (b.repr (Z ω) i) ^ 2
      = ∑ i : Fin M.rank, (W i ω) ^ 2 := by
    intro ω
    rw [← Finset.sum_attach S (fun j => (b.repr (Z ω) j) ^ 2)]
    symm
    exact Fintype.sum_equiv eqn (fun i => (W i ω) ^ 2)
      (fun j => (b.repr (Z ω) j.val) ^ 2) (fun _ => rfl)
  have hTarget : (fun ω => (Z ω : Fin n → ℝ) ⬝ᵥ (M *ᵥ (Z ω : Fin n → ℝ)))
      = (fun ω => ∑ i : Fin M.rank, (W i ω) ^ 2) := by
    funext ω; rw [hQF' ω, hSumReindex ω]
  rw [hTarget]
  exact hasLaw_sum_sq_chiSquared hr hLawW hIndepW

end QuadraticFormChiSquared

end HansenEconometrics
