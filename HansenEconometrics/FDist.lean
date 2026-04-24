import HansenEconometrics.ChiSquared
import Mathlib.Probability.Distributions.Beta

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HansenEconometrics

/-- Fisher's F distribution, packaged as the law of the ratio
`(U / q) / (V / ν)` with `U ∼ χ²(q)` and `V ∼ χ²(ν)` independent. This ratio-law object is kept
separate from the classical density-backed distribution so later theorems can bridge between the
two without entangling the Chapter 5 regression proofs. -/
noncomputable def fDist (q ν : ℕ) : Measure ℝ :=
  ((chiSquared q).prod (chiSquared ν)).map
    (fun z : ℝ × ℝ => (z.1 / (q : ℝ)) / (z.2 / (ν : ℝ)))

/-- The classical Fisher-Snedecor normalizing constant with numerator degrees of freedom `q` and
denominator degrees of freedom `ν`. This is only used when both degrees of freedom are positive;
otherwise we return `0` so the auxiliary density functions remain total. -/
noncomputable def fDensityConstant (q ν : ℕ) : ℝ :=
  if 0 < q ∧ 0 < ν then
    let qr : ℝ := q
    let νr : ℝ := ν
    ((qr / νr) ^ (qr / 2)) / ProbabilityTheory.beta (qr / 2) (νr / 2)
  else
    0

/-- The classical Fisher-Snedecor density on `ℝ`. We package the nonnegative-support condition as
an `if 0 ≤ x` guard so the function is total and measurable. -/
noncomputable def fPDFReal (q ν : ℕ) (x : ℝ) : ℝ :=
  if 0 < q ∧ 0 < ν then
    if 0 ≤ x then
      let qr : ℝ := q
      let νr : ℝ := ν
      fDensityConstant q ν * x ^ (qr / 2 - 1) * (1 + (qr / νr) * x) ^ (-(qr + νr) / 2)
    else
      0
  else
    0

/-- The classical Fisher-Snedecor density, packaged as an `ℝ≥0∞`-valued function. -/
noncomputable def fPDF (q ν : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fPDFReal q ν x)

/-- The classical density-backed Fisher-Snedecor distribution. The bridge from `fDist` to this
distribution is proved separately. -/
noncomputable def classicalFDist (q ν : ℕ) : Measure ℝ :=
  volume.withDensity (fPDF q ν)

lemma fDensityConstant_eq_zero {q ν : ℕ} (h : ¬ (0 < q ∧ 0 < ν)) :
    fDensityConstant q ν = 0 := by
  simp [fDensityConstant, h]

lemma fPDFReal_eq_zero {q ν : ℕ} (h : ¬ (0 < q ∧ 0 < ν)) (x : ℝ) :
    fPDFReal q ν x = 0 := by
  simp [fPDFReal, h]

lemma fPDF_eq_zero {q ν : ℕ} (h : ¬ (0 < q ∧ 0 < ν)) (x : ℝ) :
    fPDF q ν x = 0 := by
  simp [fPDF, fPDFReal_eq_zero h x]

lemma classicalFDist_eq_zero {q ν : ℕ} (h : ¬ (0 < q ∧ 0 < ν)) :
    classicalFDist q ν = 0 := by
  have hpdf : fPDF q ν = 0 := by
    funext x
    exact fPDF_eq_zero h x
  simp [classicalFDist, hpdf, withDensity_zero]

lemma fDensityConstant_of_pos {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) :
    fDensityConstant q ν =
      (((q : ℝ) / (ν : ℝ)) ^ ((q : ℝ) / 2)) /
        ProbabilityTheory.beta ((q : ℝ) / 2) ((ν : ℝ) / 2) := by
  simp [fDensityConstant, hq, hν]

lemma fPDFReal_of_pos {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) {x : ℝ} (hx : 0 ≤ x) :
    fPDFReal q ν x =
      fDensityConstant q ν * x ^ (((q : ℝ) / 2) - 1) *
        (1 + (((q : ℝ) / (ν : ℝ)) * x)) ^ (((-(ν : ℝ)) + (-(q : ℝ))) / 2) := by
  simp [fPDFReal, hq, hν, hx]

lemma fPDFReal_of_neg {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) {x : ℝ} (hx : x < 0) :
    fPDFReal q ν x = 0 := by
  simp [fPDFReal, hq, hν, not_le_of_gt hx]

lemma fPDFReal_nonneg (q ν : ℕ) (x : ℝ) : 0 ≤ fPDFReal q ν x := by
  by_cases h : 0 < q ∧ 0 < ν
  · rcases h with ⟨hq, hν⟩
    by_cases hx : 0 ≤ x
    · rw [fPDFReal_of_pos hq hν hx]
      refine mul_nonneg (mul_nonneg ?_ ?_) ?_
      · rw [fDensityConstant_of_pos hq hν]
        refine div_nonneg ?_ ?_
        · exact Real.rpow_nonneg (by positivity) _
        · exact le_of_lt (ProbabilityTheory.beta_pos (by positivity) (by positivity))
      · exact Real.rpow_nonneg hx _
      · exact Real.rpow_nonneg (by positivity) _
    · simp [fPDFReal, show 0 < q ∧ 0 < ν from ⟨hq, hν⟩, hx]
  · simp [fPDFReal, h]

private lemma integrable_gammaPDFReal {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) := by
  have h_nonneg : 0 ≤ᵐ[volume] gammaPDFReal a r :=
    ae_of_all _ (gammaPDFReal_nonneg ha hr)
  have h_lintegral :
      ∫⁻ x, ENNReal.ofReal (gammaPDFReal a r x) ∂ volume ≠ ∞ := by
    rw [show ∫⁻ x, ENNReal.ofReal (gammaPDFReal a r x) ∂ volume = 1 by
      simpa [gammaPDF] using (lintegral_gammaPDF_eq_one ha hr)]
    simp
  exact (lintegral_ofReal_ne_top_iff_integrable
    (stronglyMeasurable_gammaPDFReal a r).aestronglyMeasurable h_nonneg).mp h_lintegral

private lemma gammaPDFReal_scale_eq {a r c x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) :
    |c⁻¹| * gammaPDFReal a r (x / c) = gammaPDFReal a (r / c) x := by
  by_cases hx : 0 ≤ x
  · have hxc : 0 ≤ x / c := by positivity
    rw [gammaPDFReal, if_pos hxc, gammaPDFReal, if_pos hx]
    have hpow_x : (x / c) ^ (a - 1) = x ^ (a - 1) / c ^ (a - 1) := by
      rw [Real.div_rpow hx hc.le]
    have hpow_r : (r / c) ^ a = r ^ a / c ^ a := by
      rw [Real.div_rpow hr.le hc.le]
    have habs : |c⁻¹| = c⁻¹ := by
      rw [abs_of_pos (inv_pos.mpr hc)]
    have hexp : Real.exp (-(r * (x / c))) = Real.exp (-((r / c) * x)) := by
      congr 1
      field_simp [hc.ne']
    have hc_pow : c⁻¹ / c ^ (a - 1) = (c ^ a)⁻¹ := by
      calc
        c⁻¹ / c ^ (a - 1) = c⁻¹ * (c ^ (a - 1))⁻¹ := by rw [div_eq_mul_inv]
        _ = c ^ (-1 : ℝ) * c ^ (-(a - 1)) := by
              rw [show c⁻¹ = c ^ (-1 : ℝ) by rw [Real.rpow_neg_one]]
              rw [show (c ^ (a - 1))⁻¹ = c ^ (-(a - 1)) by
                symm
                exact Real.rpow_neg hc.le (a - 1)]
        _ = c ^ (-a) := by
              rw [← Real.rpow_add hc (-1 : ℝ) (-(a - 1))]
              congr 1
              ring
        _ = (c ^ a)⁻¹ := by
              exact Real.rpow_neg hc.le a
    rw [hpow_x, hpow_r, habs, hexp]
    calc
      c⁻¹ * (r ^ a / Real.Gamma a * (x ^ (a - 1) / c ^ (a - 1)) * Real.exp (-(r / c * x)))
          = (r ^ a / Real.Gamma a) * x ^ (a - 1) * Real.exp (-(r / c * x)) *
              (c⁻¹ / c ^ (a - 1)) := by
                field_simp [Real.Gamma_ne_zero]
      _ = (r ^ a / Real.Gamma a) * x ^ (a - 1) * Real.exp (-(r / c * x)) * (c ^ a)⁻¹ := by
            rw [hc_pow]
      _ = r ^ a / c ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r / c * x)) := by
            have hca_ne : c ^ a ≠ 0 := by
              exact (Real.rpow_ne_zero hc.le (by linarith : a ≠ 0)).2 hc.ne'
            field_simp [Real.Gamma_ne_zero, hca_ne]
  · have hx' : x < 0 := lt_of_not_ge hx
    have hxc' : x / c < 0 := by
      exact div_neg_of_neg_of_pos hx' hc
    simp [gammaPDFReal, hx, not_le_of_gt hxc']

private lemma gammaMeasure_map_mul_pos {a r c : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) :
    (gammaMeasure a r).map (c * ·) = gammaMeasure a (r / c) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc.ne').symm.toMeasurableEquiv
  have he_eq : (e : ℝ → ℝ) = fun y : ℝ => c⁻¹ * y := by
    funext y
    simp [e, Homeomorph.mulLeft₀, Homeomorph.toMeasurableEquiv_coe, Equiv.mulLeft₀_symm_apply,
      mul_comm]
  have he' : ∀ x, HasDerivAt (e : ℝ → ℝ) c⁻¹ x := by
    intro x
    rw [he_eq]
    simpa using (HasDerivAt.const_mul c⁻¹ (hasDerivAt_id x))
  change (gammaMeasure a r).map e.symm = gammaMeasure a (r / c)
  ext s hs
  change ((volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x))).map e.symm) s =
    (volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a (r / c) x))) s
  rw [e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs he'
    (ae_of_all _ (gammaPDFReal_nonneg ha hr)) (integrable_gammaPDFReal ha hr)]
  rw [withDensity_apply _ hs]
  have h_nonneg : 0 ≤ᵐ[volume.restrict s] gammaPDFReal a (r / c) :=
    ae_of_all _ (gammaPDFReal_nonneg ha (div_pos hr hc))
  have h_int : IntegrableOn (gammaPDFReal a (r / c)) s :=
    (integrable_gammaPDFReal ha (div_pos hr hc)).integrableOn
  rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  congr 1
  refine setIntegral_congr_fun hs ?_
  intro x hx
  rw [he_eq]
  simpa [div_eq_mul_inv, mul_comm] using
    (gammaPDFReal_scale_eq ha hr hc (x := x))

private lemma lintegral_chiSquared_ratio_eq_gamma
    {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν)
    {v : ℝ} (hv : 0 < v) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ u, φ ((u / (q : ℝ)) / (v / (ν : ℝ))) ∂ chiSquared q =
      ∫⁻ x, φ x *
        ENNReal.ofReal
          (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x) ∂ volume := by
  let c : ℝ := (ν : ℝ) / ((q : ℝ) * v)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hfun :
      (fun u : ℝ => (u / (q : ℝ)) / (v / (ν : ℝ))) = fun u : ℝ => c * u := by
    funext u
    dsimp [c]
    field_simp [show ((q : ℝ) * v) ≠ 0 by positivity]
  have hmap :
      (chiSquared q).map (fun u : ℝ => (u / (q : ℝ)) / (v / (ν : ℝ))) =
        gammaMeasure ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) := by
    rw [hfun, chiSquared_eq]
    have hbase :=
      gammaMeasure_map_mul_pos (a := ((q : ℝ) / 2)) (r := (1 / 2 : ℝ)) (c := c)
        (by positivity) (by positivity) hc
    have hrate : (1 / 2 : ℝ) / c = ((q : ℝ) * v) / (2 * (ν : ℝ)) := by
      dsimp [c]
      field_simp [show (ν : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hν)]
    have hrate' : ((2 : ℝ)⁻¹) / c = ((q : ℝ) * v) / (2 * (ν : ℝ)) := by
      simpa [one_div] using hrate
    simpa [hrate'] using hbase
  calc
    ∫⁻ u, φ ((u / (q : ℝ)) / (v / (ν : ℝ))) ∂ chiSquared q
      = ∫⁻ x, φ x ∂ ((chiSquared q).map (fun u : ℝ => (u / (q : ℝ)) / (v / (ν : ℝ)))) := by
          rw [lintegral_map' hφ.aemeasurable (by fun_prop)]
    _ = ∫⁻ x, φ x ∂ gammaMeasure ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) := by
          rw [hmap]
    _ = ∫⁻ x, φ x *
          ENNReal.ofReal
            (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x) ∂ volume := by
          rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul₀
            (hf := by
              exact (by fun_prop : AEMeasurable
                (fun x =>
                  ENNReal.ofReal
                    (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x))
                volume))
            (hg := hφ.aemeasurable)]
          simp [gammaPDF, Pi.mul_apply, mul_comm]

private lemma integral_Ioi_fKernel_eq_fPDFReal
    {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) (x : ℝ) :
    ∫ v in Set.Ioi (0 : ℝ),
      gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
        gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v =
      fPDFReal q ν x := by
  by_cases hx : 0 ≤ x
  · let a : ℝ := (q : ℝ) / 2
    let b : ℝ := (ν : ℝ) / 2
    let lmbda : ℝ := (1 + ((q : ℝ) / (ν : ℝ)) * x) / 2
    let C : ℝ :=
      ((((q : ℝ) / (2 * (ν : ℝ))) ^ a) / Real.Gamma a) *
        ((((1 / 2 : ℝ) ^ b) / Real.Gamma b) * x ^ (a - 1))
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hb : 0 < b := by
      dsimp [b]
      positivity
    have hlmbda : 0 < lmbda := by
      dsimp [lmbda]
      positivity
    have hνr_ne : (ν : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hν)
    calc
      ∫ v in Set.Ioi (0 : ℝ),
          gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
            gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v
        = ∫ v in Set.Ioi (0 : ℝ), C * (v ^ ((a + b) - 1) * Real.exp (-(lmbda * v))) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro v hv
            have hv0 : 0 ≤ v := hv.le
            simp only [gammaPDFReal, if_pos hx, if_pos hv0]
            have hrate_split :
                (((q : ℝ) * v) / (2 * (ν : ℝ))) ^ a =
                  (((q : ℝ) / (2 * (ν : ℝ))) ^ a) * v ^ a := by
              have hbase :
                  (((q : ℝ) * v) / (2 * (ν : ℝ))) = ((q : ℝ) / (2 * (ν : ℝ))) * v := by
                field_simp [hνr_ne]
              rw [hbase, Real.mul_rpow (by positivity) hv0]
            have hpow_v :
                v ^ a * v ^ (b - 1) = v ^ ((a + b) - 1) := by
              rw [← Real.rpow_add hv a (b - 1)]
              congr 1
              ring
            have hexp :
                Real.exp (-((((q : ℝ) * v) / (2 * (ν : ℝ))) * x)) *
                  Real.exp (-((1 / 2 : ℝ) * v)) =
                  Real.exp (-(lmbda * v)) := by
                rw [← Real.exp_add]
                congr 1
                dsimp [lmbda]
                field_simp [hνr_ne]
                ring
            calc
              ((((q : ℝ) * v) / (2 * (ν : ℝ))) ^ a / Real.Gamma a *
                  x ^ (a - 1) * Real.exp (-((((q : ℝ) * v) / (2 * (ν : ℝ))) * x))) *
                  (((1 / 2 : ℝ) ^ b / Real.Gamma b) * v ^ (b - 1) * Real.exp (-((1 / 2 : ℝ) * v)))
                = C * (v ^ a * v ^ (b - 1)) *
                    (Real.exp (-((((q : ℝ) * v) / (2 * (ν : ℝ))) * x)) *
                      Real.exp (-((1 / 2 : ℝ) * v))) := by
                    dsimp [C]
                    rw [hrate_split]
                    ring_nf
              _ = C * (v ^ ((a + b) - 1) * Real.exp (-(lmbda * v))) := by
                    rw [hpow_v, hexp]
                    ring
      _ = C * ((1 / lmbda) ^ (a + b) * Real.Gamma (a + b)) := by
            rw [integral_const_mul]
            congr 1
            exact Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0 < a + b by positivity) hlmbda
      _ = fPDFReal q ν x := by
            rw [fPDFReal_of_pos hq hν hx, fDensityConstant_of_pos hq hν]
            dsimp [C, a, b, lmbda]
            have hbase_nonneg : 0 ≤ 1 + (q : ℝ) / (ν : ℝ) * x := by
              positivity
            have hlmbda_rpow :
                (1 / ((1 + (q : ℝ) / (ν : ℝ) * x) / 2)) ^ (((q : ℝ) / 2) + ((ν : ℝ) / 2)) =
                  (2 : ℝ) ^ (((q : ℝ) / 2) + ((ν : ℝ) / 2)) *
                    (1 + (q : ℝ) / (ν : ℝ) * x) ^
                      (-((((q : ℝ) / 2) + ((ν : ℝ) / 2)))) := by
              rw [show 1 / ((1 + (q : ℝ) / (ν : ℝ) * x) / 2) =
                  2 / (1 + (q : ℝ) / (ν : ℝ) * x) by
                    field_simp [hνr_ne]
                  ]
              rw [Real.div_rpow (by norm_num : 0 ≤ (2 : ℝ)) hbase_nonneg]
              rw [Real.rpow_neg hbase_nonneg]
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
            have hscale :
                (((q : ℝ) / (2 * (ν : ℝ))) ^ ((q : ℝ) / 2)) =
                  (((q : ℝ) / (ν : ℝ)) ^ ((q : ℝ) / 2)) * (1 / 2 : ℝ) ^ ((q : ℝ) / 2) := by
              have hbase :
                  ((q : ℝ) / (2 * (ν : ℝ))) = ((q : ℝ) / (ν : ℝ)) * (1 / 2 : ℝ) := by
                field_simp [hνr_ne]
              rw [hbase, Real.mul_rpow (by positivity) (by norm_num : 0 ≤ (1 / 2 : ℝ))]
            have htwo_cancel :
                (1 / 2 : ℝ) ^ ((q : ℝ) / 2) * (1 / 2 : ℝ) ^ ((ν : ℝ) / 2) *
                    (2 : ℝ) ^ (((q : ℝ) / 2) + ((ν : ℝ) / 2)) = 1 := by
              rw [← Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ)) ((q : ℝ) / 2) ((ν : ℝ) / 2)]
              rw [show (1 / 2 : ℝ) ^ (((q : ℝ) / 2) + ((ν : ℝ) / 2)) =
                  (2 : ℝ) ^ (-((((q : ℝ) / 2) + ((ν : ℝ) / 2))) ) by
                    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
                    rw [← Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]]
              rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))
                (-((((q : ℝ) / 2) + ((ν : ℝ) / 2)))) ((((q : ℝ) / 2) + ((ν : ℝ) / 2)))]
              simp
            rw [hlmbda_rpow, hscale]
            have hsum :
                (((q : ℝ) / 2) + ((ν : ℝ) / 2)) = (((q : ℝ) + (ν : ℝ)) / 2) := by ring
            have hbeta_ne :
                ProbabilityTheory.beta ((q : ℝ) / 2) ((ν : ℝ) / 2) ≠ 0 :=
              ne_of_gt (ProbabilityTheory.beta_pos ha hb)
            have htwo_cancel' :
                (1 / 2 : ℝ) ^ ((q : ℝ) / 2) * (1 / 2 : ℝ) ^ ((ν : ℝ) / 2) *
                    (2 : ℝ) ^ (((q : ℝ) + (ν : ℝ)) / 2) = 1 := by
              simpa [hsum] using htwo_cancel
            have hgamma' :
                Real.Gamma (((q : ℝ) + (ν : ℝ)) / 2) =
                  Real.Gamma ((q : ℝ) / 2) * Real.Gamma ((ν : ℝ) / 2) /
                    ProbabilityTheory.beta ((q : ℝ) / 2) ((ν : ℝ) / 2) := by
              rw [ProbabilityTheory.beta]
              field_simp [Real.Gamma_ne_zero]
            have hneg_sum :
                -((((q : ℝ) / 2) + ((ν : ℝ) / 2))) = -(((q : ℝ) + (ν : ℝ)) / 2) := by
              ring
            have hneg_rhs :
                (((-(ν : ℝ)) + (-(q : ℝ))) / 2) = -(((q : ℝ) + (ν : ℝ)) / 2) := by
              ring
            rw [hsum, hgamma', hneg_rhs]
            let xpow : ℝ := x ^ (((q : ℝ) / 2) - 1)
            let tail : ℝ := (1 + (q : ℝ) / (ν : ℝ) * x) ^ (-(((q : ℝ) + (ν : ℝ)) / 2))
            rw [show x ^ (((q : ℝ) / 2) - 1) = xpow by rfl]
            rw [show (1 + (q : ℝ) / (ν : ℝ) * x) ^ (-(((q : ℝ) + (ν : ℝ)) / 2)) = tail by rfl]
            calc
              (((q : ℝ) / (ν : ℝ)) ^ ((q : ℝ) / 2) * (1 / 2 : ℝ) ^ ((q : ℝ) / 2)) /
                    Real.Gamma ((q : ℝ) / 2) *
                    (((1 / 2 : ℝ) ^ ((ν : ℝ) / 2) / Real.Gamma ((ν : ℝ) / 2)) * xpow) *
                    ((2 : ℝ) ^ (((q : ℝ) + (ν : ℝ)) / 2) * tail *
                      (Real.Gamma ((q : ℝ) / 2) * Real.Gamma ((ν : ℝ) / 2) /
                        ProbabilityTheory.beta ((q : ℝ) / 2) ((ν : ℝ) / 2)))
                =
                  (((q : ℝ) / (ν : ℝ)) ^ ((q : ℝ) / 2) *
                      (((1 / 2 : ℝ) ^ ((q : ℝ) / 2) *
                          (1 / 2 : ℝ) ^ ((ν : ℝ) / 2) *
                          (2 : ℝ) ^ (((q : ℝ) + (ν : ℝ)) / 2)) *
                        (xpow * tail))) /
                    ProbabilityTheory.beta ((q : ℝ) / 2) ((ν : ℝ) / 2) := by
                      dsimp [xpow, tail]
                      field_simp [Real.Gamma_ne_zero, hbeta_ne]
              _ = (((q : ℝ) / (ν : ℝ)) ^ ((q : ℝ) / 2) * (xpow * tail)) /
                    ProbabilityTheory.beta ((q : ℝ) / 2) ((ν : ℝ) / 2) := by
                      rw [htwo_cancel']
                      simp
              _ = (((q : ℝ) / (ν : ℝ)) ^ ((q : ℝ) / 2)) /
                    ProbabilityTheory.beta ((q : ℝ) / 2) ((ν : ℝ) / 2) * xpow * tail := by
                      field_simp [hbeta_ne]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [fPDFReal_of_neg hq hν hx']
    have hzero :
        ∫ v in Set.Ioi (0 : ℝ),
          gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
            gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v
          = ∫ v in Set.Ioi (0 : ℝ), (0 : ℝ) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro v hv
            simp [gammaPDFReal, hx]
    simpa using hzero

private lemma fKernel_eq_const_rpow_exp
    {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) {x v : ℝ}
    (hx : 0 ≤ x) (hv : 0 < v) :
    gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
        gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v
      =
        ((((q : ℝ) / (2 * (ν : ℝ))) ^ (((q : ℝ) / 2)) / Real.Gamma ((q : ℝ) / 2)) *
          ((((1 / 2 : ℝ) ^ (((ν : ℝ) / 2))) / Real.Gamma ((ν : ℝ) / 2)) *
            x ^ (((q : ℝ) / 2) - 1))) *
          (v ^ ((((q : ℝ) + (ν : ℝ)) / 2) - 1) *
            Real.exp (-((((1 + ((q : ℝ) / (ν : ℝ) * x)) / 2) * v)))) := by
  let a : ℝ := (q : ℝ) / 2
  let b : ℝ := (ν : ℝ) / 2
  let lmbda : ℝ := (1 + ((q : ℝ) / (ν : ℝ)) * x) / 2
  let C : ℝ :=
    ((((q : ℝ) / (2 * (ν : ℝ))) ^ a) / Real.Gamma a) *
      ((((1 / 2 : ℝ) ^ b) / Real.Gamma b) * x ^ (a - 1))
  have hνr_ne : (ν : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hν)
  have hv0 : 0 ≤ v := hv.le
  simp only [gammaPDFReal, if_pos hx, if_pos hv0]
  have hrate_split :
      (((q : ℝ) * v) / (2 * (ν : ℝ))) ^ a =
        (((q : ℝ) / (2 * (ν : ℝ))) ^ a) * v ^ a := by
    have hbase :
        (((q : ℝ) * v) / (2 * (ν : ℝ))) = ((q : ℝ) / (2 * (ν : ℝ))) * v := by
      field_simp [hνr_ne]
    rw [hbase, Real.mul_rpow (by positivity) hv0]
  have hpow_v :
      v ^ a * v ^ (b - 1) = v ^ ((a + b) - 1) := by
    rw [← Real.rpow_add hv a (b - 1)]
    congr 1
    ring
  have hexp :
      Real.exp (-((((q : ℝ) * v) / (2 * (ν : ℝ))) * x)) *
        Real.exp (-((1 / 2 : ℝ) * v)) =
        Real.exp (-(lmbda * v)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [lmbda]
    field_simp [hνr_ne]
    ring
  calc
    ((((q : ℝ) * v) / (2 * (ν : ℝ))) ^ a / Real.Gamma a *
        x ^ (a - 1) * Real.exp (-((((q : ℝ) * v) / (2 * (ν : ℝ))) * x))) *
        (((1 / 2 : ℝ) ^ b / Real.Gamma b) * v ^ (b - 1) * Real.exp (-((1 / 2 : ℝ) * v)))
      = C * (v ^ a * v ^ (b - 1)) *
          (Real.exp (-((((q : ℝ) * v) / (2 * (ν : ℝ))) * x)) *
            Real.exp (-((1 / 2 : ℝ) * v))) := by
              dsimp [C]
              rw [hrate_split]
              ring_nf
    _ = C * (v ^ ((a + b) - 1) * Real.exp (-(lmbda * v))) := by
          rw [hpow_v, hexp]
          ring
    _ =
        ((((q : ℝ) / (2 * (ν : ℝ))) ^ (((q : ℝ) / 2)) / Real.Gamma ((q : ℝ) / 2)) *
          ((((1 / 2 : ℝ) ^ (((ν : ℝ) / 2))) / Real.Gamma ((ν : ℝ) / 2)) *
            x ^ (((q : ℝ) / 2) - 1))) *
          (v ^ ((((q : ℝ) + (ν : ℝ)) / 2) - 1) *
            Real.exp (-((((1 + ((q : ℝ) / (ν : ℝ) * x)) / 2) * v)))) := by
          dsimp [C, a, b, lmbda]
          ring

private lemma integrableOn_Ioi_fKernel
    {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) (x : ℝ) :
    IntegrableOn
      (fun v =>
        gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
          gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v)
      (Set.Ioi (0 : ℝ)) := by
  by_cases hx : 0 ≤ x
  · let a : ℝ := (((q : ℝ) + (ν : ℝ)) / 2)
    let r : ℝ := (1 + ((q : ℝ) / (ν : ℝ)) * x) / 2
    let C : ℝ :=
      ((((q : ℝ) / (2 * (ν : ℝ))) ^ (((q : ℝ) / 2))) / Real.Gamma ((q : ℝ) / 2)) *
        ((((1 / 2 : ℝ) ^ (((ν : ℝ) / 2))) / Real.Gamma ((ν : ℝ) / 2)) *
          x ^ (((q : ℝ) / 2) - 1))
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hbase0 :
        IntegrableOn (fun v : ℝ => v ^ (a - 1) * Real.exp (-(r * v))) (Set.Ioi (0 : ℝ)) := by
      simpa using
        (integrableOn_rpow_mul_exp_neg_mul_rpow
          (show -1 < a - 1 by linarith) (by norm_num : (1 : ℝ) ≤ 1) hr)
    have hbase :
        IntegrableOn (fun v : ℝ => C * (v ^ (a - 1) * Real.exp (-(r * v)))) (Set.Ioi (0 : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbase0.const_mul C
    refine IntegrableOn.congr_fun hbase ?_ measurableSet_Ioi
    intro v hv
    simpa [a, r, C] using (fKernel_eq_const_rpow_exp hq hν hx hv).symm
  · refine IntegrableOn.congr_fun (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi (0 : ℝ))) ?_ measurableSet_Ioi
    intro v hv
    simp [gammaPDFReal, hx]

private lemma lintegral_Ioi_fKernel_eq_fPDF
    {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) (x : ℝ) :
    ∫⁻ v in Set.Ioi (0 : ℝ),
      ENNReal.ofReal
        (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
          gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v) =
      ENNReal.ofReal (fPDFReal q ν x) := by
  have h_int :
      Integrable
        (fun v =>
          gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
            gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_Ioi_fKernel hq hν x
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun v =>
        gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
          gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    exact Filter.Eventually.of_forall fun v hv =>
      let hvpos : 0 < v := hv
      let hr : 0 < (((q : ℝ) * v) / (2 * (ν : ℝ))) := by
        positivity
      mul_nonneg
        (gammaPDFReal_nonneg
          (a := ((q : ℝ) / 2)) (r := (((q : ℝ) * v) / (2 * (ν : ℝ))))
          (by positivity) hr _)
        (gammaPDFReal_nonneg (by positivity) (by positivity) _)
  rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  simpa using congrArg ENNReal.ofReal (integral_Ioi_fKernel_eq_fPDFReal hq hν x)

private lemma measurable_f_kernel_fixed {q ν : ℕ} (x : ℝ) :
    Measurable (fun v : ℝ =>
      ENNReal.ofReal (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x)) := by
  by_cases hx : 0 ≤ x
  · simp [gammaPDFReal, hx]
    fun_prop
  · simp [gammaPDFReal, hx]

private lemma measurable_f_kernel_rate_fixed {q ν : ℕ} (v : ℝ) :
    Measurable (fun x : ℝ =>
      ENNReal.ofReal (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x)) := by
  exact (measurable_gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ)))).ennreal_ofReal

private lemma measurable_fPDFReal (q ν : ℕ) : Measurable (fPDFReal q ν) := by
  by_cases h : 0 < q ∧ 0 < ν
  · rcases h with ⟨hq, hν⟩
    let s : Set ℝ := {x : ℝ | 0 ≤ x}
    have hs : MeasurableSet s := (isClosed_le continuous_const continuous_id).measurableSet
    let g : ℝ → ℝ := fun x =>
      fDensityConstant q ν * x ^ (((q : ℝ) / 2) - 1) *
        (1 + ((q : ℝ) / (ν : ℝ)) * x) ^ ((-((q : ℝ) + (ν : ℝ))) / 2)
    have hbranch :
        Measurable g := by
      fun_prop
    have hpiece : Measurable (s.piecewise g (fun _ : ℝ => 0)) :=
      hbranch.piecewise hs measurable_const
    convert hpiece using 1
    ext x
    by_cases hx' : 0 ≤ x
    · simp [fPDFReal, hq, hν, s, g, hx']
    · simp [fPDFReal, hq, hν, s, g, hx']
  · have hz : fPDFReal q ν = fun _ : ℝ => 0 := by
      funext x
      simp [fPDFReal, h]
    rw [hz]
    exact measurable_const

private lemma measurable_fPDF (q ν : ℕ) : Measurable (fPDF q ν) := by
  exact ENNReal.measurable_ofReal.comp (measurable_fPDFReal q ν)

private lemma measurable_f_kernel {q ν : ℕ} :
    Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * z.1) / (2 * (ν : ℝ))) z.2)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const measurable_snd
  · fun_prop

private lemma lintegral_f_kernel_eq_fPDF {q ν : ℕ}
    (hq : 0 < q) (hν : 0 < ν) (x : ℝ) :
    ∫⁻ v,
      gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
        ENNReal.ofReal
          (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x) ∂ volume =
      ENNReal.ofReal (fPDFReal q ν x) := by
  have hv0_ae : ∀ᵐ v : ℝ ∂ volume, v ≠ 0 := by
    have hnotmem : ∀ᵐ v : ℝ ∂ volume, v ∉ ({0} : Set ℝ) :=
      (measure_eq_zero_iff_ae_notMem.1 (by simp))
    simpa using hnotmem
  have hcongr :
      (fun v =>
        gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
          ENNReal.ofReal
            (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x))
        =ᵐ[volume]
      Set.indicator (Set.Ioi (0 : ℝ)) (fun v =>
        ENNReal.ofReal
          (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
            gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v)) := by
    filter_upwards [hv0_ae] with v hv0
    rcases lt_or_gt_of_ne hv0 with hvneg | hvpos
    · rw [gammaPDF_of_neg hvneg]
      simp [Set.indicator, hvneg, gammaPDFReal, not_le_of_gt hvneg]
    · have hgamma_eq :
          gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v =
            ENNReal.ofReal (gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v) := by
          rw [gammaPDF_of_nonneg hvpos.le]
          simp [gammaPDFReal, hvpos.le]
      rw [hgamma_eq]
      have hγ_nonneg :
          0 ≤ gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v :=
        gammaPDFReal_nonneg (by positivity) (by positivity) v
      calc
        ENNReal.ofReal (gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v) *
              ENNReal.ofReal
                (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x)
            =
              ENNReal.ofReal
                (gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
                  gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x) := by
                  rw [← ENNReal.ofReal_mul hγ_nonneg]
        _ =
              ENNReal.ofReal
                (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
                  gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v) := by
                  simp [mul_comm]
        _ =
              (Set.Ioi (0 : ℝ)).indicator
                (fun v =>
                  ENNReal.ofReal
                    (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x *
                      gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) v)) v := by
                  simp [Set.indicator, hvpos]
  rw [lintegral_congr_ae hcongr, lintegral_indicator measurableSet_Ioi]
  exact lintegral_Ioi_fKernel_eq_fPDF hq hν x

private lemma ae_f_outer_eq {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    (fun v =>
      gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
        ∫⁻ u, φ ((u / (q : ℝ)) / (v / (ν : ℝ))) ∂ chiSquared q)
      =ᵐ[volume]
    (fun v =>
      ∫⁻ x, gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
        (φ x *
          ENNReal.ofReal
            (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x)) ∂ volume) := by
  have hv0_ae : ∀ᵐ v : ℝ ∂ volume, v ≠ 0 := by
    have hnotmem : ∀ᵐ v : ℝ ∂ volume, v ∉ ({0} : Set ℝ) :=
      (measure_eq_zero_iff_ae_notMem.1 (by simp))
    simpa using hnotmem
  filter_upwards [hv0_ae] with v hv0
  rcases lt_or_gt_of_ne hv0 with hvneg | hvpos
  · have hgamma : gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v = 0 := gammaPDF_of_neg hvneg
    rw [hgamma]
    simp
  · rw [lintegral_chiSquared_ratio_eq_gamma hq hν hvpos hφ]
    have hmeas :
        AEMeasurable
          (fun x =>
            φ x *
              ENNReal.ofReal
                (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x))
          volume :=
      hφ.aemeasurable.mul ((measurable_f_kernel_rate_fixed (q := q) (ν := ν) v).aemeasurable)
    have hconst := lintegral_const_mul'' (gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v) hmeas
    rw [← hconst]

private lemma lintegral_f_double_eq {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v, ∫⁻ x,
      gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
        (φ x *
          ENNReal.ofReal
            (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x)) ∂ volume ∂ volume =
      ∫⁻ x, φ x * ENNReal.ofReal (fPDFReal q ν x) ∂ volume := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun v x =>
    gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
      (φ x *
        ENNReal.ofReal
          (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x))
  let G : ℝ × ℝ → ℝ≥0∞ := fun z => F z.1 z.2
  have hG : Measurable G := by
    dsimp [G, F]
    exact (((measurable_gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ)).ennreal_ofReal).comp measurable_fst).mul
      ((hφ.comp measurable_snd).mul measurable_f_kernel)
  calc
    ∫⁻ v, ∫⁻ x, F v x ∂ volume ∂ volume
      = ∫⁻ z, G z ∂ volume.prod volume := by
          rw [lintegral_lintegral (hf := by simpa [G, F] using hG.aemeasurable)]
    _ = ∫⁻ x, ∫⁻ v, G (v, x) ∂ volume ∂ volume := by
          rw [lintegral_prod_symm' _ hG]
    _ = ∫⁻ x, φ x * ENNReal.ofReal (fPDFReal q ν x) ∂ volume := by
          refine lintegral_congr_ae (ae_of_all _ ?_)
          intro x
          have hinner : ∫⁻ v, F v x ∂ volume = φ x * ENNReal.ofReal (fPDFReal q ν x) := by
            calc
              ∫⁻ v, F v x ∂ volume
                = ∫⁻ v,
                    φ x *
                      (gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
                        ENNReal.ofReal
                          (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x)) ∂ volume := by
                      refine lintegral_congr_ae (ae_of_all _ fun v => ?_)
                      simp [F, mul_assoc, mul_left_comm, mul_comm]
              _ =
                  φ x *
                    ∫⁻ v,
                      gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
                        ENNReal.ofReal
                          (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x) ∂ volume := by
                    have hmeas :
                        AEMeasurable
                          (fun v =>
                            gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
                              ENNReal.ofReal
                                (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x))
                          volume :=
                      (((measurable_gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ)).ennreal_ofReal).aemeasurable).mul
                        ((measurable_f_kernel_fixed (q := q) (ν := ν) x).aemeasurable)
                    simpa using (lintegral_const_mul'' (φ x) hmeas)
              _ = φ x * ENNReal.ofReal (fPDFReal q ν x) := by
                    rw [lintegral_f_kernel_eq_fPDF hq hν x]
          simpa [G, F] using hinner

theorem ratio_prod_map_eq_classicalFDist {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) :
    ((chiSquared q).prod (chiSquared ν)).map
      (fun z : ℝ × ℝ => (z.1 / (q : ℝ)) / (z.2 / (ν : ℝ))) =
    classicalFDist q ν := by
  refine Measure.ext_of_lintegral _ ?_
  intro φ hφ
  let ratio : ℝ × ℝ → ℝ := fun z => (z.1 / (q : ℝ)) / (z.2 / (ν : ℝ))
  have hratio : Measurable ratio := by
    dsimp [ratio]
    fun_prop
  haveI : IsProbabilityMeasure (chiSquared q) := isProbabilityMeasure_chiSquared hq
  haveI : IsProbabilityMeasure (chiSquared ν) := isProbabilityMeasure_chiSquared hν
  rw [lintegral_map' hφ.aemeasurable hratio.aemeasurable]
  rw [lintegral_prod_symm _ (by
    dsimp [ratio]
    fun_prop)]
  rw [chiSquared_eq (k := ν), gammaMeasure]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀
    (hf := by
      simpa [gammaPDF] using
        (measurable_gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ)).ennreal_ofReal.aemeasurable)
    (h'f := ae_of_all _ fun v : ℝ => by simp [gammaPDF])]
  have houter :
      (fun v =>
        (gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) *
          fun y => ∫⁻ u, φ (ratio (u, y)) ∂ chiSquared q) v)
        =ᵐ[volume]
      (fun v =>
        ∫⁻ x,
          gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) v *
            (φ x *
              ENNReal.ofReal
                (gammaPDFReal ((q : ℝ) / 2) (((q : ℝ) * v) / (2 * (ν : ℝ))) x)) ∂ volume) := by
    simpa [Pi.mul_apply, ratio] using (ae_f_outer_eq hq hν hφ)
  rw [lintegral_congr_ae houter]
  rw [lintegral_f_double_eq hq hν hφ]
  rw [classicalFDist, lintegral_withDensity_eq_lintegral_mul₀
    (hf := (measurable_fPDF q ν).aemeasurable) (hg := hφ.aemeasurable)]
  simp [fPDF, mul_comm, mul_left_comm, mul_assoc]

theorem fDist_eq_classicalFDist {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) :
    fDist q ν = classicalFDist q ν := by
  rw [fDist, ratio_prod_map_eq_classicalFDist hq hν]

lemma isProbabilityMeasure_fDist {q ν : ℕ} (hq : 0 < q) (hν : 0 < ν) :
    IsProbabilityMeasure (fDist q ν) := by
  haveI : IsProbabilityMeasure (chiSquared q) := isProbabilityMeasure_chiSquared hq
  haveI : IsProbabilityMeasure (chiSquared ν) := isProbabilityMeasure_chiSquared hν
  change IsProbabilityMeasure
    (((chiSquared q).prod (chiSquared ν)).map
      (fun z : ℝ × ℝ => (z.1 / (q : ℝ)) / (z.2 / (ν : ℝ))))
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem hasLaw_ratio_chiSquared_fDist
    {q ν : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {U V : Ω → ℝ}
    (hq : 0 < q) (_hν : 0 < ν)
    (hU : HasLaw U (chiSquared q) μ)
    (hV : HasLaw V (chiSquared ν) μ)
    (hInd : U ⟂ᵢ[μ] V) :
    HasLaw (fun ω => (U ω / (q : ℝ)) / (V ω / (ν : ℝ))) (fDist q ν) μ := by
  haveI : IsProbabilityMeasure (chiSquared q) := isProbabilityMeasure_chiSquared hq
  haveI : IsProbabilityMeasure μ := hU.isProbabilityMeasure
  have hPair :
      HasLaw (fun ω => (U ω, V ω)) ((chiSquared q).prod (chiSquared ν)) μ := by
    refine ⟨hU.aemeasurable.prodMk hV.aemeasurable, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hInd,
      hU.map_eq, hV.map_eq]
  have hMap :
      HasLaw (fun z : ℝ × ℝ => (z.1 / (q : ℝ)) / (z.2 / (ν : ℝ))) (fDist q ν)
        (((chiSquared q).prod (chiSquared ν)) : Measure (ℝ × ℝ)) := by
    exact ⟨by fun_prop, rfl⟩
  simpa [fDist] using hMap.comp hPair

end HansenEconometrics
