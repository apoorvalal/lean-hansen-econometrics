import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

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

theorem hasLaw_add_chiSquared
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {Ω : Type*} [MeasureSpace Ω]
    {X Y : Ω → ℝ}
    (hX : HasLaw X (chiSquared a)) (hY : HasLaw Y (chiSquared b))
    (hIndep : IndepFun X Y) :
    HasLaw (fun ω => X ω + Y ω) (chiSquared (a + b)) := by
  sorry

theorem hasLaw_sum_sq_chiSquared
    {k : ℕ} (hk : 0 < k)
    {Ω : Type*} [MeasureSpace Ω]
    {W : Fin k → Ω → ℝ}
    (hLaw : ∀ i, HasLaw (W i) (gaussianReal 0 1))
    (hIndep : ProbabilityTheory.iIndepFun W) :
    HasLaw (fun ω => ∑ i, (W i ω)^2) (chiSquared k) := by
  sorry

end HansenEconometrics
