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
  · -- Case t ≥ 0: equate CDFs via substitution s = u², Jacobian 2u
    push Not at ht
    -- TODO: prove via:
    --   LHS = gaussianReal 0 1 (Icc (-√t) (√t))
    --       = ENNReal.ofReal (2 * ∫ u in [0, √t], gaussianPDFReal 0 1 u)  (Gaussian symmetry)
    --   RHS = ENNReal.ofReal (∫ s in [0,t], gammaPDFReal (1/2)(1/2) s)
    --       = ENNReal.ofReal (∫ u in [0,√t], gammaPDFReal (1/2)(1/2)(u²) * 2u)  (subst s=u²)
    --       = ENNReal.ofReal (∫ u in [0,√t], 2 * gaussianPDFReal 0 1 u)          (jacobian_pdf_eq)
    --       = LHS
    sorry

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
