import HansenEconometrics.ChiSquared
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Probability.Distributions.Beta

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HansenEconometrics

/-- The classical Student-t normalizing constant with `ν` degrees of freedom. This is only used
for positive `ν`; when `ν = 0` we return `0` so the auxiliary density functions remain total. -/
noncomputable def studentTDensityConstant (ν : ℕ) : ℝ :=
  if _hν : 0 < ν then
    let νr : ℝ := ν
    Real.Gamma ((νr + 1) / 2) / (Real.sqrt (νr * Real.pi) * Real.Gamma (νr / 2))
  else
    0

/-- The classical Student-t density on `ℝ`. -/
noncomputable def studentTPDFReal (ν : ℕ) (x : ℝ) : ℝ :=
  if _hν : 0 < ν then
    let νr : ℝ := ν
    studentTDensityConstant ν * (1 + x ^ 2 / νr) ^ (-(νr + 1) / 2)
  else
    0

/-- The classical Student-t density, packaged as an `ℝ≥0∞`-valued function. -/
noncomputable def studentTPDF (ν : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (studentTPDFReal ν x)

/-- The classical density-backed Student-t measure. The bridge from the ratio-law `studentT` to
this density-backed measure is proved separately. -/
noncomputable def classicalStudentT (ν : ℕ) : Measure ℝ :=
  volume.withDensity (studentTPDF ν)

/-- An explicit lower bound for
`∫ x in Set.Icc (0 : ℝ) 2, (1 + x^2 / ν)^(-((ν + 1) / 2))`.

It comes from the odd degree-11 Taylor polynomial of `u ↦ (1 + u)^(-((ν + 1) / 2))`
evaluated at `u = x^2 / ν` and integrated termwise over `[0,2]`. The numerical corollary used in
Hansen's Theorem 5.10 only needs this explicit rational function and its monotonicity in
step-two degrees of freedom. -/
noncomputable def studentTTwoCoverageKernelLowerBound (ν : ℕ) : ℝ :=
  let νr : ℝ := ν
  (2 : ℝ) *
    (189153462893 * νr ^ 11
      - 6221980234 * νr ^ 10
      - 33704396034 * νr ^ 9
      + 46648125660 * νr ^ 8
      - 858581153094 * νr ^ 7
      - 10779981221604 * νr ^ 6
      - 119962831564796 * νr ^ 5
      - 868559973795800 * νr ^ 4
      - 4153989541890474 * νr ^ 3
      - 12067017360146892 * νr ^ 2
      - 18370548806877540 * νr
      - 9699203657543400) /
    (316234143225 * νr ^ 11)

/-- The explicit lower bound for the symmetric central Student-t interval mass on `[-2,2]`
obtained from `studentTTwoCoverageKernelLowerBound`. -/
noncomputable def studentTTwoCoverageLowerBound (ν : ℕ) : ℝ :=
  2 * studentTDensityConstant ν * studentTTwoCoverageKernelLowerBound ν

/-- The Student-t kernel on `[0,2]` whose integral gives the central mass on `[-2,2]` after
multiplying by the density constant. -/
noncomputable def studentTTwoCoverageKernel (ν : ℕ) (x : ℝ) : ℝ :=
  (1 + x ^ 2 / (ν : ℝ)) ^ (-(((ν : ℝ) + 1) / 2))

/-- The degree-11 Taylor lower polynomial for `studentTTwoCoverageKernel`, expressed via the
Taylor polynomial of `u ↦ (1 + u)^(-((ν+1)/2))` at `u = 0` and then pulled back along
`u = x^2 / ν`. -/
noncomputable def studentTTwoCoverageTaylorLower (ν : ℕ) (x : ℝ) : ℝ :=
  let a : ℝ := (((ν : ℝ) + 1) / 2)
  let f : ℝ → ℝ := fun u => (1 + u) ^ (-a)
  ∑ k ∈ Finset.range 12,
    ((((Nat.factorial k : ℕ) : ℝ)⁻¹) * (x ^ 2 / (ν : ℝ)) ^ k) * iteratedDeriv k f 0

lemma studentTDensityConstant_eq_zero {ν : ℕ} (hν : ¬ 0 < ν) :
    studentTDensityConstant ν = 0 := by
  simp [studentTDensityConstant, hν]

lemma studentTPDFReal_eq_zero {ν : ℕ} (hν : ¬ 0 < ν) (x : ℝ) :
    studentTPDFReal ν x = 0 := by
  simp [studentTPDFReal, hν]

lemma studentTPDF_eq_zero {ν : ℕ} (hν : ¬ 0 < ν) (x : ℝ) :
    studentTPDF ν x = 0 := by
  simp [studentTPDF, studentTPDFReal_eq_zero hν x]

lemma classicalStudentT_eq_zero {ν : ℕ} (hν : ¬ 0 < ν) :
    classicalStudentT ν = 0 := by
  have hpdf : studentTPDF ν = 0 := by
    funext x
    exact studentTPDF_eq_zero hν x
  simp [classicalStudentT, hpdf, withDensity_zero]

lemma studentTDensityConstant_of_pos {ν : ℕ} (hν : 0 < ν) :
    studentTDensityConstant ν =
      Real.Gamma (((ν : ℝ) + 1) / 2) /
        (Real.sqrt ((ν : ℝ) * Real.pi) * Real.Gamma ((ν : ℝ) / 2)) := by
  simp [studentTDensityConstant, hν]

lemma studentTPDFReal_of_pos {ν : ℕ} (hν : 0 < ν) (x : ℝ) :
    studentTPDFReal ν x =
      studentTDensityConstant ν * (1 + x ^ 2 / (ν : ℝ)) ^ (-((ν : ℝ) + 1) / 2) := by
  simp [studentTPDFReal, hν]

@[fun_prop]
lemma measurable_studentTPDFReal (ν : ℕ) : Measurable (studentTPDFReal ν) := by
  unfold studentTPDFReal
  split_ifs <;> fun_prop

@[fun_prop]
lemma stronglyMeasurable_studentTPDFReal (ν : ℕ) :
    StronglyMeasurable (studentTPDFReal ν) :=
  (measurable_studentTPDFReal ν).stronglyMeasurable

@[fun_prop]
lemma measurable_studentTPDF (ν : ℕ) : Measurable (studentTPDF ν) := by
  simpa [studentTPDF] using (measurable_studentTPDFReal ν).ennreal_ofReal

@[fun_prop]
lemma measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) := by
  simpa [gammaPDF] using (measurable_gammaPDFReal a r).ennreal_ofReal

lemma studentTPDFReal_nonneg (ν : ℕ) (x : ℝ) : 0 ≤ studentTPDFReal ν x := by
  by_cases hν : 0 < ν
  · rw [studentTPDFReal_of_pos hν]
    refine mul_nonneg ?_ ?_
    · rw [studentTDensityConstant_of_pos hν]
      refine div_nonneg ?_ ?_
      · exact Real.Gamma_nonneg_of_nonneg (by positivity)
      · refine mul_nonneg (Real.sqrt_nonneg _) ?_
        exact Real.Gamma_nonneg_of_nonneg (by positivity)
    · exact Real.rpow_nonneg (by positivity) _
  · simp [studentTPDFReal, hν]

lemma studentTDensityConstant_nonneg (ν : ℕ) : 0 ≤ studentTDensityConstant ν := by
  by_cases hν : 0 < ν
  · rw [studentTDensityConstant_of_pos hν]
    refine div_nonneg ?_ ?_
    · exact Real.Gamma_nonneg_of_nonneg (by positivity)
    · refine mul_nonneg (Real.sqrt_nonneg _) ?_
      exact Real.Gamma_nonneg_of_nonneg (by positivity)
  · simp [studentTDensityConstant, hν]

lemma studentTDensityConstant_pos {ν : ℕ} (hν : 0 < ν) :
    0 < studentTDensityConstant ν := by
  rw [studentTDensityConstant_of_pos hν]
  refine div_pos (Real.Gamma_pos_of_pos (by positivity)) ?_
  refine mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.Gamma_pos_of_pos (by positivity))

lemma studentTDensityConstant_step_two {ν : ℕ} (hν : 0 < ν) :
    studentTDensityConstant (ν + 2) =
      (((ν : ℝ) + 1) / Real.sqrt ((ν : ℝ) * ((ν : ℝ) + 2))) * studentTDensityConstant ν := by
  have hνr : (ν : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hν)
  have hνr_pos : 0 < (ν : ℝ) := by exact_mod_cast hν
  rw [studentTDensityConstant_of_pos (show 0 < ν + 2 by omega),
    studentTDensityConstant_of_pos hν]
  have hgamma_num :
      Real.Gamma (((((ν + 2 : ℕ) : ℝ) + 1) / 2)) =
        ((((ν : ℝ) + 1) / 2) * Real.Gamma (((ν : ℝ) + 1) / 2)) := by
    have : ((((ν + 2 : ℕ) : ℝ) + 1) / 2) = (((ν : ℝ) + 1) / 2) + 1 := by
      norm_num
      norm_num
      ring
    rw [this, Real.Gamma_add_one]
    nlinarith
  have hgamma_den :
      Real.Gamma ((((ν + 2 : ℕ) : ℝ) / 2)) =
        (((ν : ℝ) / 2) * Real.Gamma ((ν : ℝ) / 2)) := by
    have : (((ν + 2 : ℕ) : ℝ) / 2) = ((ν : ℝ) / 2) + 1 := by
      norm_num
      ring
    rw [this, Real.Gamma_add_one]
    positivity
  have hsqrt_add :
      Real.sqrt ((((ν + 2 : ℕ) : ℝ) * Real.pi)) =
        Real.sqrt ((ν : ℝ) + 2) * Real.sqrt Real.pi := by
    rw [show (((ν + 2 : ℕ) : ℝ) * Real.pi) = (((ν : ℝ) + 2) * Real.pi) by norm_num]
    rw [Real.sqrt_mul (by positivity)]
  have hsqrt :
      Real.sqrt ((ν : ℝ) * ((ν : ℝ) + 2)) =
        Real.sqrt (ν : ℝ) * Real.sqrt ((ν : ℝ) + 2) := by
    rw [Real.sqrt_mul hνr_pos.le]
  have hsqrt_nupi :
      Real.sqrt ((ν : ℝ) * Real.pi) = Real.sqrt (ν : ℝ) * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul hνr_pos.le]
  rw [hgamma_num, hgamma_den, hsqrt_add, hsqrt, hsqrt_nupi]
  field_simp [hνr, Real.Gamma_pos_of_pos (by positivity), Real.sqrt_ne_zero'.2 hνr_pos,
    Real.sqrt_ne_zero'.2 (by positivity : 0 < (ν : ℝ) + 2),
    Real.sqrt_ne_zero'.2 Real.pi_pos]
  rw [Real.sq_sqrt hνr_pos.le]

lemma studentTDensityConstant_step_two_gt {ν : ℕ} (hν : 0 < ν) :
    studentTDensityConstant ν < studentTDensityConstant (ν + 2) := by
  rw [studentTDensityConstant_step_two hν]
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hratio :
      1 < (((ν : ℝ) + 1) / Real.sqrt ((ν : ℝ) * ((ν : ℝ) + 2))) := by
    have hsqrt_pos : 0 < Real.sqrt ((ν : ℝ) * ((ν : ℝ) + 2)) := by positivity
    rw [one_lt_div hsqrt_pos]
    have hsq :
        ((ν : ℝ) * ((ν : ℝ) + 2)) < (((ν : ℝ) + 1) : ℝ) ^ 2 := by
      ring_nf
      nlinarith
    have hsqrt_lt : Real.sqrt ((ν : ℝ) * ((ν : ℝ) + 2)) < ((ν : ℝ) + 1) := by
      exact (Real.sqrt_lt' (by positivity)).2 hsq
    linarith
  have hpos : 0 < studentTDensityConstant ν := by
    rw [studentTDensityConstant_of_pos hν]
    refine div_pos (Real.Gamma_pos_of_pos (by positivity)) ?_
    refine mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  nlinarith

lemma studentTTwoCoverageKernelLowerBound_step_two_le {ν : ℕ} (hν : 0 < ν) :
    studentTTwoCoverageKernelLowerBound ν ≤ studentTTwoCoverageKernelLowerBound (ν + 2) := by
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hdiff :
      studentTTwoCoverageKernelLowerBound (ν + 2) - studentTTwoCoverageKernelLowerBound ν =
        8 *
          (3110990117 * (ν : ℝ) ^ 20
            + 95924198374 * (ν : ℝ) ^ 19
            + 1130389557216 * (ν : ℝ) ^ 18
            + 8904325583196 * (ν : ℝ) ^ 17
            + 83928134822190 * (ν : ℝ) ^ 16
            + 1081489233519468 * (ν : ℝ) ^ 15
            + 12671750425859632 * (ν : ℝ) ^ 14
            + 113016676497481480 * (ν : ℝ) ^ 13
            + 751404550195734430 * (ν : ℝ) ^ 12
            + 3779739657746819212 * (ν : ℝ) ^ 11
            + 14748743555820178304 * (ν : ℝ) ^ 10
            + 45684315305825194752 * (ν : ℝ) ^ 9
            + 113272934261919732144 * (ν : ℝ) ^ 8
            + 223813346784916139776 * (ν : ℝ) ^ 7
            + 349395183283828125824 * (ν : ℝ) ^ 6
            + 424868584391217900032 * (ν : ℝ) ^ 5
            + 393510725496266270464 * (ν : ℝ) ^ 4
            + 267859817755697756160 * (ν : ℝ) ^ 3
            + 126192172077667897344 * (ν : ℝ) ^ 2
            + 36718678488763514880 * (ν : ℝ)
            + 4965992272662220800) /
        (316234143225 * (ν : ℝ) ^ 11 * ((ν : ℝ) + 2) ^ 11) := by
    dsimp [studentTTwoCoverageKernelLowerBound]
    norm_num
    field_simp
    ring_nf
  rw [← sub_nonneg]
  rw [hdiff]
  positivity

lemma sqrt_sixty_one_gt_781_div_100 : (781 : ℝ) / 100 < Real.sqrt 61 := by
  refine Real.lt_sqrt_of_sq_lt ?_
  norm_num

lemma sqrt_sixty_two_gt_3937_div_500 : (3937 : ℝ) / 500 < Real.sqrt 62 := by
  refine Real.lt_sqrt_of_sq_lt ?_
  norm_num

lemma studentTDensityConstant_sixty_one :
    studentTDensityConstant 61 =
      72057594037927936 * Real.sqrt 61 / (450883717216034179 * Real.pi) := by
  rw [studentTDensityConstant_of_pos (by norm_num : 0 < 61)]
  norm_num
  have hΓ : Real.Gamma ((61 : ℝ) / 2) =
      (((Nat.doubleFactorial 59 : ℕ) * Real.sqrt Real.pi / (2 ^ 30)) : ℝ) := by
    convert (Real.Gamma_nat_add_half 30) using 1 <;> norm_num
  rw [hΓ]
  field_simp [Real.pi_pos.ne']
  ring_nf
  have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  rw [hsqpi]
  field_simp [Real.pi_pos.ne']
  norm_num

lemma studentTDensityConstant_sixty_two :
    studentTDensityConstant 62 =
      14544636039226909 * Real.sqrt 62 / 288230376151711744 := by
  rw [studentTDensityConstant_of_pos (by norm_num : 0 < 62)]
  norm_num
  have hΓ : Real.Gamma ((63 : ℝ) / 2) =
      (((Nat.doubleFactorial 61 : ℕ) * Real.sqrt Real.pi / (2 ^ 31)) : ℝ) := by
    convert (Real.Gamma_nat_add_half 31) using 1 <;> norm_num
  rw [hΓ]
  field_simp
  ring_nf
  norm_num

lemma studentTTwoCoverageLowerBound_sixty_one :
    studentTTwoCoverageLowerBound 61 =
      12839193878435967851780581165975117758464 * Real.sqrt 61 /
        (33597873425796219577310349341837952744273 * Real.pi) := by
  rw [studentTTwoCoverageLowerBound, studentTDensityConstant_sixty_one]
  norm_num [studentTTwoCoverageKernelLowerBound]
  ring_nf

lemma studentTTwoCoverageLowerBound_sixty_two :
    studentTTwoCoverageLowerBound 62 =
      1767366759723588097819154232198439 * Real.sqrt 62 / 14646989706585683659367480482070528 := by
  rw [studentTTwoCoverageLowerBound, studentTDensityConstant_sixty_two]
  norm_num [studentTTwoCoverageKernelLowerBound]
  ring_nf

lemma studentTTwoCoverageLowerBound_sixty_one_ge_nineteen_twentieths :
    (19 : ℝ) / 20 ≤ studentTTwoCoverageLowerBound 61 := by
  rw [studentTTwoCoverageLowerBound_sixty_one]
  have hsqrt : (781 : ℝ) / 100 ≤ Real.sqrt 61 := le_of_lt sqrt_sixty_one_gt_781_div_100
  have hpi : Real.pi ≤ (3927 : ℝ) / 1250 := by
    linarith [Real.pi_lt_d4]
  have hmain :
      (19 : ℝ) / 20 ≤
        12839193878435967851780581165975117758464 * ((781 : ℝ) / 100) /
          (33597873425796219577310349341837952744273 * ((3927 : ℝ) / 1250)) := by
    norm_num
  calc
    (19 : ℝ) / 20
      ≤ 12839193878435967851780581165975117758464 * ((781 : ℝ) / 100) /
          (33597873425796219577310349341837952744273 * ((3927 : ℝ) / 1250)) := hmain
    _ ≤ 12839193878435967851780581165975117758464 * Real.sqrt 61 /
          (33597873425796219577310349341837952744273 * ((3927 : ℝ) / 1250)) := by
            gcongr
    _ ≤ 12839193878435967851780581165975117758464 * Real.sqrt 61 /
          (33597873425796219577310349341837952744273 * Real.pi) := by
            have hden_pos : 0 < (33597873425796219577310349341837952744273 : ℝ) := by positivity
            have hpi_pos : 0 < Real.pi := Real.pi_pos
            have hrat_pos : 0 < ((3927 : ℝ) / 1250) := by positivity
            gcongr

lemma studentTTwoCoverageLowerBound_sixty_two_ge_nineteen_twentieths :
    (19 : ℝ) / 20 ≤ studentTTwoCoverageLowerBound 62 := by
  rw [studentTTwoCoverageLowerBound_sixty_two]
  have hsqrt : (3937 : ℝ) / 500 ≤ Real.sqrt 62 := le_of_lt sqrt_sixty_two_gt_3937_div_500
  have hmain :
      (19 : ℝ) / 20 ≤
        1767366759723588097819154232198439 * ((3937 : ℝ) / 500) /
          14646989706585683659367480482070528 := by
    norm_num
  calc
    (19 : ℝ) / 20
      ≤ 1767366759723588097819154232198439 * ((3937 : ℝ) / 500) /
          14646989706585683659367480482070528 := hmain
    _ ≤ 1767366759723588097819154232198439 * Real.sqrt 62 /
          14646989706585683659367480482070528 := by
            gcongr

private lemma studentTTwoCoverageKernelLowerBound_sixty_one_nonneg :
    0 ≤ studentTTwoCoverageKernelLowerBound 61 := by
  norm_num [studentTTwoCoverageKernelLowerBound]

private lemma studentTTwoCoverageKernelLowerBound_sixty_two_nonneg :
    0 ≤ studentTTwoCoverageKernelLowerBound 62 := by
  norm_num [studentTTwoCoverageKernelLowerBound]

private lemma studentTTwoCoverageKernelLowerBound_sixty_one_step_chain (m : ℕ) :
    studentTTwoCoverageKernelLowerBound 61 ≤
      studentTTwoCoverageKernelLowerBound (61 + 2 * m) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        studentTTwoCoverageKernelLowerBound 61
            ≤ studentTTwoCoverageKernelLowerBound (61 + 2 * m) := ih
        _ ≤ studentTTwoCoverageKernelLowerBound ((61 + 2 * m) + 2) :=
            studentTTwoCoverageKernelLowerBound_step_two_le (by omega)
        _ = studentTTwoCoverageKernelLowerBound (61 + 2 * (m + 1)) := by
            congr 1

private lemma studentTTwoCoverageKernelLowerBound_sixty_two_step_chain (m : ℕ) :
    studentTTwoCoverageKernelLowerBound 62 ≤
      studentTTwoCoverageKernelLowerBound (62 + 2 * m) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        studentTTwoCoverageKernelLowerBound 62
            ≤ studentTTwoCoverageKernelLowerBound (62 + 2 * m) := ih
        _ ≤ studentTTwoCoverageKernelLowerBound ((62 + 2 * m) + 2) :=
            studentTTwoCoverageKernelLowerBound_step_two_le (by omega)
        _ = studentTTwoCoverageKernelLowerBound (62 + 2 * (m + 1)) := by
            congr 1

lemma studentTTwoCoverageKernelLowerBound_nonneg_of_ge_sixty_one
    {ν : ℕ} (hν : 61 ≤ ν) :
    0 ≤ studentTTwoCoverageKernelLowerBound ν := by
  rcases Nat.even_or_odd' (ν - 61) with ⟨m, hm | hm⟩
  · have hν_eq : ν = 61 + 2 * m := by omega
    calc
      0 ≤ studentTTwoCoverageKernelLowerBound 61 :=
        studentTTwoCoverageKernelLowerBound_sixty_one_nonneg
      _ ≤ studentTTwoCoverageKernelLowerBound (61 + 2 * m) :=
        studentTTwoCoverageKernelLowerBound_sixty_one_step_chain m
      _ = studentTTwoCoverageKernelLowerBound ν := by rw [hν_eq]
  · have hν_eq : ν = 62 + 2 * m := by omega
    calc
      0 ≤ studentTTwoCoverageKernelLowerBound 62 :=
        studentTTwoCoverageKernelLowerBound_sixty_two_nonneg
      _ ≤ studentTTwoCoverageKernelLowerBound (62 + 2 * m) :=
        studentTTwoCoverageKernelLowerBound_sixty_two_step_chain m
      _ = studentTTwoCoverageKernelLowerBound ν := by rw [hν_eq]

lemma studentTTwoCoverageLowerBound_step_two_le_of_ge_sixty_one
    {ν : ℕ} (hν : 61 ≤ ν) :
    studentTTwoCoverageLowerBound ν ≤ studentTTwoCoverageLowerBound (ν + 2) := by
  -- Step-two monotonicity for the explicit lower bound used in Theorem 5.10: both the Student-t
  -- density constant and the integrated Taylor lower polynomial improve when `ν` increases by `2`.
  have hνpos : 0 < ν := by omega
  have hc_le :
      studentTDensityConstant ν ≤ studentTDensityConstant (ν + 2) :=
    le_of_lt (studentTDensityConstant_step_two_gt hνpos)
  have hk_le :
      studentTTwoCoverageKernelLowerBound ν ≤ studentTTwoCoverageKernelLowerBound (ν + 2) :=
    studentTTwoCoverageKernelLowerBound_step_two_le hνpos
  have hk_nonneg :
      0 ≤ studentTTwoCoverageKernelLowerBound ν :=
    studentTTwoCoverageKernelLowerBound_nonneg_of_ge_sixty_one hν
  have hc_next_nonneg : 0 ≤ studentTDensityConstant (ν + 2) :=
    studentTDensityConstant_nonneg (ν + 2)
  have hprod :
      studentTDensityConstant ν * studentTTwoCoverageKernelLowerBound ν ≤
        studentTDensityConstant (ν + 2) * studentTTwoCoverageKernelLowerBound (ν + 2) :=
    mul_le_mul hc_le hk_le hk_nonneg hc_next_nonneg
  dsimp [studentTTwoCoverageLowerBound]
  nlinarith

private lemma studentTTwoCoverageLowerBound_sixty_one_step_chain (m : ℕ) :
    studentTTwoCoverageLowerBound 61 ≤ studentTTwoCoverageLowerBound (61 + 2 * m) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        studentTTwoCoverageLowerBound 61
            ≤ studentTTwoCoverageLowerBound (61 + 2 * m) := ih
        _ ≤ studentTTwoCoverageLowerBound ((61 + 2 * m) + 2) :=
            studentTTwoCoverageLowerBound_step_two_le_of_ge_sixty_one (by omega)
        _ = studentTTwoCoverageLowerBound (61 + 2 * (m + 1)) := by
            congr 1

private lemma studentTTwoCoverageLowerBound_sixty_two_step_chain (m : ℕ) :
    studentTTwoCoverageLowerBound 62 ≤ studentTTwoCoverageLowerBound (62 + 2 * m) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        studentTTwoCoverageLowerBound 62
            ≤ studentTTwoCoverageLowerBound (62 + 2 * m) := ih
        _ ≤ studentTTwoCoverageLowerBound ((62 + 2 * m) + 2) :=
            studentTTwoCoverageLowerBound_step_two_le_of_ge_sixty_one (by omega)
        _ = studentTTwoCoverageLowerBound (62 + 2 * (m + 1)) := by
            congr 1

lemma studentTTwoCoverageLowerBound_ge_nineteen_twentieths_of_ge_sixty_one
    {ν : ℕ} (hν : 61 ≤ ν) :
    (19 : ℝ) / 20 ≤ studentTTwoCoverageLowerBound ν := by
  -- Parity argument for Theorem 5.10: start from the verified `ν = 61` and `ν = 62` base cases,
  -- then iterate the step-two monotonicity lemma along the odd and even subsequences separately.
  rcases Nat.even_or_odd' (ν - 61) with ⟨m, hm | hm⟩
  · have hν_eq : ν = 61 + 2 * m := by omega
    calc
      (19 : ℝ) / 20 ≤ studentTTwoCoverageLowerBound 61 :=
        studentTTwoCoverageLowerBound_sixty_one_ge_nineteen_twentieths
      _ ≤ studentTTwoCoverageLowerBound (61 + 2 * m) :=
        studentTTwoCoverageLowerBound_sixty_one_step_chain m
      _ = studentTTwoCoverageLowerBound ν := by rw [hν_eq]
  · have hν_eq : ν = 62 + 2 * m := by omega
    calc
      (19 : ℝ) / 20 ≤ studentTTwoCoverageLowerBound 62 :=
        studentTTwoCoverageLowerBound_sixty_two_ge_nineteen_twentieths
      _ ≤ studentTTwoCoverageLowerBound (62 + 2 * m) :=
        studentTTwoCoverageLowerBound_sixty_two_step_chain m
      _ = studentTTwoCoverageLowerBound ν := by rw [hν_eq]

private lemma descPochhammer_eval_neg_nonneg_twelve {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ (descPochhammer ℝ 12).eval (-a) := by
  rw [descPochhammer_eval_eq_prod_range]
  have hprod :
      (∏ j ∈ Finset.range 12, (-a - (j : ℝ))) =
        ∏ j ∈ Finset.range 12, (a + (j : ℝ)) := by
    norm_num [Finset.prod_range_succ]
    ring
  rw [hprod]
  exact Finset.prod_nonneg fun j hj => by positivity

private lemma one_add_rpow_taylor_lower_eleven {a u : ℝ}
    (ha : 0 < a) (hu : 0 ≤ u) :
    (∑ k ∈ Finset.range 12,
      (((Nat.factorial k : ℕ) : ℝ)⁻¹ * u ^ k) *
        iteratedDeriv k (fun z : ℝ => (1 + z) ^ (-a)) 0) ≤
      (1 + u) ^ (-a) := by
  -- Truncate at degree `11` so the remainder is governed by the `12`th derivative; that
  -- derivative is nonnegative on `[0, ∞)`, so the Taylor polynomial is a lower bound.
  by_cases hu0 : u = 0
  · subst u
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      simp [Nat.ne_of_gt hkpos]
    · simp
  · have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    let f : ℝ → ℝ := fun z => (1 + z) ^ (-a)
    have hf : ContDiffOn ℝ 12 f (Set.Icc (0 : ℝ) u) := by
      have hbase : ∀ y ∈ Set.Icc (0 : ℝ) u, (1 : ℝ) + y ≠ 0 := by
        intro y hy
        nlinarith [hy.1]
      exact (contDiffOn_const.add contDiffOn_id).rpow_const_of_ne hbase
    obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (n := 11) hu_pos hf
    have htaylor :
        taylorWithinEval f 11 (Set.Icc (0 : ℝ) u) 0 u =
          ∑ k ∈ Finset.range 12,
            (((Nat.factorial k : ℕ) : ℝ)⁻¹ * u ^ k) *
              iteratedDeriv k f 0 := by
      rw [taylor_within_apply]
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hwithin :
          iteratedDerivWithin k f (Set.Icc (0 : ℝ) u) 0 = iteratedDeriv k f 0 := by
        have hcd : ContDiffAt ℝ k f 0 := by
          have hbase : (1 : ℝ) + 0 ≠ 0 := by norm_num
          exact (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne hbase
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu_pos) hcd
          ⟨le_rfl, hu⟩
      rw [hwithin]
      simp [f, smul_eq_mul]
    have hiter_nonneg : 0 ≤ iteratedDeriv 12 f y := by
      have hiter :
          iteratedDeriv 12 f y =
            (descPochhammer ℝ 12).eval (-a) * (1 + y) ^ (-a - 12) := by
        change iteratedDeriv 12 (fun z : ℝ => (1 + z) ^ (-a)) y =
          (descPochhammer ℝ 12).eval (-a) * (1 + y) ^ (-a - 12)
        rw [show (fun z : ℝ => (1 + z) ^ (-a)) = (fun z : ℝ => (z + 1) ^ (-a)) by
          funext z
          ring_nf]
        rw [show
            iteratedDeriv 12 (fun z : ℝ => (z + 1) ^ (-a)) y =
              iteratedDeriv 12 (fun z : ℝ => z ^ (-a)) (y + 1) by
              exact congrFun
                (iteratedDeriv_comp_add_const 12 (fun z : ℝ => z ^ (-a)) 1) y]
        rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
        ring_nf
      rw [hiter]
      exact mul_nonneg (descPochhammer_eval_neg_nonneg_twelve ha.le)
        (Real.rpow_nonneg (show 0 ≤ 1 + y by linarith [hy.1]) _)
    have hremainder_nonneg :
        0 ≤ (1 + u) ^ (-a) - taylorWithinEval f 11 (Set.Icc (0 : ℝ) u) 0 u := by
      have hrem' :
          (1 + u) ^ (-a) - taylorWithinEval f 11 (Set.Icc (0 : ℝ) u) 0 u =
            iteratedDeriv 12 f y * u ^ 12 / (12 : ℕ).factorial := by
        simpa [f] using hrem
      rw [hrem']
      exact div_nonneg (mul_nonneg hiter_nonneg (pow_nonneg hu 12)) (by positivity)
    rw [htaylor] at hremainder_nonneg
    linarith

lemma studentTTwoCoverageTaylorLower_le_kernel {ν : ℕ} (hν : 0 < ν)
    {x : ℝ} (_hx : x ∈ Set.Icc (0 : ℝ) 2) :
    studentTTwoCoverageTaylorLower ν x ≤ studentTTwoCoverageKernel ν x := by
  let a : ℝ := (((ν : ℝ) + 1) / 2)
  let u : ℝ := x ^ 2 / (ν : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hmain := one_add_rpow_taylor_lower_eleven (a := a) (u := u) ha hu
  simpa [studentTTwoCoverageTaylorLower, studentTTwoCoverageKernel, a, u] using hmain

lemma integral_studentTTwoCoverageTaylorLower_eq_kernelLowerBound {ν : ℕ} (hν : 0 < ν) :
    ∫ x in (0 : ℝ)..2, studentTTwoCoverageTaylorLower ν x =
      studentTTwoCoverageKernelLowerBound ν := by
  have hνr : (ν : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hν)
  simp only [studentTTwoCoverageTaylorLower]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [show ∀ k : ℕ, ∀ x : ℝ,
        ((((Nat.factorial k : ℕ) : ℝ)⁻¹ * (x ^ 2 / (ν : ℝ)) ^ k) *
            iteratedDeriv k (fun u : ℝ => (1 + u) ^ (-(((ν : ℝ) + 1) / 2))) 0) =
          ((((Nat.factorial k : ℕ) : ℝ)⁻¹ *
              ((ν : ℝ)⁻¹ ^ k) *
              iteratedDeriv k (fun u : ℝ => (1 + u) ^ (-(((ν : ℝ) + 1) / 2))) 0) *
            x ^ (2 * k)) by
        intro k x
        rw [div_eq_mul_inv, mul_pow, ← pow_mul]
        ring]
    simp_rw [intervalIntegral.integral_const_mul]
    simp_rw [integral_pow]
    have hiter0 : ∀ k : ℕ,
        iteratedDeriv k (fun u : ℝ => (1 + u) ^ (-(((ν : ℝ) + 1) / 2))) 0 =
          (descPochhammer ℝ k).eval (-(((ν : ℝ) + 1) / 2)) := by
      intro k
      change iteratedDeriv k (fun u : ℝ => (1 + u) ^ (-(((ν : ℝ) + 1) / 2))) 0 =
        (descPochhammer ℝ k).eval (-(((ν : ℝ) + 1) / 2))
      rw [show
          (fun u : ℝ => (1 + u) ^ (-(((ν : ℝ) + 1) / 2))) =
            (fun u : ℝ => (u + 1) ^ (-(((ν : ℝ) + 1) / 2))) by
            funext u
            ring_nf]
      rw [show
          iteratedDeriv k (fun u : ℝ => (u + 1) ^ (-(((ν : ℝ) + 1) / 2))) 0 =
            iteratedDeriv k (fun u : ℝ => u ^ (-(((ν : ℝ) + 1) / 2))) (0 + 1) by
            exact congrFun
              (iteratedDeriv_comp_add_const k
                (fun u : ℝ => u ^ (-(((ν : ℝ) + 1) / 2))) 1) 0]
      rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
      norm_num
    simp_rw [hiter0]
    norm_num [studentTTwoCoverageKernelLowerBound, descPochhammer_eval_eq_prod_range,
      Finset.sum_range_succ, Finset.prod_range_succ]
    field_simp [hνr]
    ring
  · intro k hk
    exact (by
      fun_prop :
        Continuous fun x : ℝ =>
          (((Nat.factorial k : ℕ) : ℝ)⁻¹ * (x ^ 2 / (ν : ℝ)) ^ k) *
            iteratedDeriv k (fun u : ℝ => (1 + u) ^ (-(((ν : ℝ) + 1) / 2))) 0).intervalIntegrable
          0 2

lemma studentTTwoCoverageKernelLowerBound_le_integral_kernel {ν : ℕ} (hν : 0 < ν) :
    studentTTwoCoverageKernelLowerBound ν ≤
      ∫ x in (0 : ℝ)..2, studentTTwoCoverageKernel ν x := by
  rw [← integral_studentTTwoCoverageTaylorLower_eq_kernelLowerBound hν]
  refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 2) (μ := volume)
    (by norm_num)
    ?_ ?_ ?_
  · exact (by
      unfold studentTTwoCoverageTaylorLower
      fun_prop :
        Continuous fun x : ℝ => studentTTwoCoverageTaylorLower ν x).intervalIntegrable 0 2
  · have hcont : Continuous fun x : ℝ => studentTTwoCoverageKernel ν x := by
      dsimp [studentTTwoCoverageKernel]
      refine (by fun_prop :
        Continuous fun x : ℝ => 1 + x ^ 2 / (ν : ℝ)).rpow_const ?_
      intro x
      exact Or.inl (ne_of_gt (by positivity : 0 < 1 + x ^ 2 / (ν : ℝ)))
    exact hcont.intervalIntegrable 0 2
  · intro x hx
    exact studentTTwoCoverageTaylorLower_le_kernel hν hx

private lemma integral_Ioo_zero_one_betaKernel_eq_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Set.Ioo (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (b - 1) = ProbabilityTheory.beta a b := by
  have hlin :
      ∫⁻ x in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal
            ((1 / ProbabilityTheory.beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)) = 1 := by
    simpa [ProbabilityTheory.lintegral_betaPDF] using
      (ProbabilityTheory.lintegral_betaPDF_eq_one (α := a) (β := b) ha hb)
  have hkernel_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => (1 / ProbabilityTheory.beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact one_div_nonneg.2 (le_of_lt (ProbabilityTheory.beta_pos ha hb))
    · exact Real.rpow_nonneg hx.1.le _
    · exact Real.rpow_nonneg (by linarith [hx.2]) _
  have hkernel_meas :
      Measurable fun x : ℝ =>
        (1 / ProbabilityTheory.beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) := by
    fun_prop
  have hscaled :
      ∫ x in Set.Ioo (0 : ℝ) 1,
          (1 / ProbabilityTheory.beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) = 1 := by
    have hlin' :
        ∫⁻ x in Set.Ioo (0 : ℝ) 1,
            ENNReal.ofReal
              (((ProbabilityTheory.beta a b)⁻¹) * x ^ (a - 1) * (1 - x) ^ (b - 1)) = 1 := by
      simpa [one_div] using hlin
    have hlin_toReal :
        (∫⁻ x in Set.Ioo (0 : ℝ) 1,
            ENNReal.ofReal
              ((1 / ProbabilityTheory.beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1))).toReal = 1 := by
      rw [show
          (∫⁻ x in Set.Ioo (0 : ℝ) 1,
              ENNReal.ofReal
                ((1 / ProbabilityTheory.beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1))) =
            ∫⁻ x in Set.Ioo (0 : ℝ) 1,
              ENNReal.ofReal
                (((ProbabilityTheory.beta a b)⁻¹) * x ^ (a - 1) * (1 - x) ^ (b - 1)) by
            simp [one_div]]
      rw [hlin']
      norm_num
    rw [integral_eq_lintegral_of_nonneg_ae hkernel_nonneg hkernel_meas.aestronglyMeasurable]
    exact hlin_toReal
  have hbeta_ne : ProbabilityTheory.beta a b ≠ 0 := ne_of_gt (ProbabilityTheory.beta_pos ha hb)
  have hscaled' :
      ∫ x in Set.Ioo (0 : ℝ) 1,
          (1 / ProbabilityTheory.beta a b) *
            (x ^ (a - 1) * (1 - x) ^ (b - 1)) = 1 := by
    simpa [mul_assoc] using hscaled
  rw [integral_const_mul] at hscaled'
  field_simp [hbeta_ne] at hscaled'
  exact hscaled'

lemma studentTPDFReal_abs (ν : ℕ) (x : ℝ) :
    studentTPDFReal ν |x| = studentTPDFReal ν x := by
  by_cases hν : 0 < ν
  · rw [studentTPDFReal_of_pos hν, studentTPDFReal_of_pos hν]
    congr 1
    simp
  · simp [studentTPDFReal, hν]

private lemma image_Ioo_zero_one_div_one_sub :
    (fun u : ℝ => u / (1 - u)) '' Set.Ioo (0 : ℝ) 1 = Set.Ioi (0 : ℝ) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hden : 0 < 1 - u := sub_pos.mpr hu.2
    exact div_pos hu.1 hden
  · intro hz
    have hz0 : 0 < z := hz
    refine ⟨z / (1 + z), ?_, ?_⟩
    · constructor
      · have hden : 0 < 1 + z := by nlinarith [hz0]
        exact div_pos hz hden
      · have hden : 0 < 1 + z := by nlinarith [hz0]
        have : z / (1 + z) - 1 < 0 := by
          field_simp [hden.ne']
          linarith
        linarith
    · have hden : (1 : ℝ) + z ≠ 0 := by nlinarith [hz0]
      field_simp [hden]
      ring

private lemma integral_Ioi_studentTKernel_eq_beta {ν : ℕ} (hν : 0 < ν) :
    ∫ z in Set.Ioi (0 : ℝ), z ^ (-(1 / 2 : ℝ)) * (1 + z) ^ (-(((ν : ℝ) + 1) / 2)) =
      ProbabilityTheory.beta (1 / 2) ((ν : ℝ) / 2) := by
  let f : ℝ → ℝ := fun u => u / (1 - u)
  let f' : ℝ → ℝ := fun u => ((1 - u) ^ 2)⁻¹
  let g : ℝ → ℝ := fun z => z ^ (-(1 / 2 : ℝ)) * (1 + z) ^ (-(((ν : ℝ) + 1) / 2))
  have hf' : ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt f (f' u) (Set.Ioo (0 : ℝ) 1) u := by
    intro u hu
    have hderiv :
        HasDerivAt (fun u : ℝ => u / (1 - u)) (((1 - u) ^ 2)⁻¹) u := by
      have hu1 : 1 - u ≠ 0 := by nlinarith [hu.2]
      have hquot :=
        (hasDerivAt_id u).div ((hasDerivAt_const u (c := (1 : ℝ))).sub (hasDerivAt_id u)) hu1
      simpa [f, f', div_eq_mul_inv, sub_eq_add_neg, hu1, pow_two] using hquot
    exact hderiv.hasDerivWithinAt
  have hmono : MonotoneOn f (Set.Ioo (0 : ℝ) 1) := by
    intro u hu v hv huv
    have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
    have hv1 : 0 < 1 - v := sub_pos.mpr hv.2
    rw [show f u = u / (1 - u) by rfl, show f v = v / (1 - v) by rfl]
    field_simp [hu1.ne', hv1.ne']
    nlinarith
  have hmain :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      (s := Set.Ioo (0 : ℝ) 1) measurableSet_Ioo hf' hmono g
  rw [image_Ioo_zero_one_div_one_sub] at hmain
  calc
    ∫ z in Set.Ioi (0 : ℝ), g z
      = ∫ u in Set.Ioo (0 : ℝ) 1, f' u * g (f u) := hmain
    _ = ∫ u in Set.Ioo (0 : ℝ) 1, u ^ ((1 / 2 : ℝ) - 1) * (1 - u) ^ (((ν : ℝ) / 2) - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioo ?_
      intro u hu
      have hu0 : 0 < u := hu.1
      have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
      have hsum : 1 + u / (1 - u) = (1 - u)⁻¹ := by
        field_simp [hu1.ne']
        ring
      have hratio :
          (u / (1 - u)) ^ (-(1 / 2 : ℝ)) =
            u ^ ((1 / 2 : ℝ) - 1) * (1 - u) ^ (1 / 2 : ℝ) := by
        rw [Real.div_rpow hu0.le hu1.le (-(1 / 2 : ℝ))]
        rw [show ((1 / 2 : ℝ) - 1) = -(1 / 2 : ℝ) by ring]
        rw [Real.rpow_neg hu0.le (1 / 2 : ℝ), Real.rpow_neg hu1.le (1 / 2 : ℝ)]
        simp [div_eq_mul_inv, mul_comm]
      simp only [f, f', g]
      rw [hratio, hsum, Real.rpow_neg_eq_inv_rpow, inv_inv]
      have huPow :
          ((1 - u) ^ 2)⁻¹ * (1 - u) ^ (1 / 2 : ℝ) * (1 - u) ^ (((ν : ℝ) + 1) / 2) =
            (1 - u) ^ (((ν : ℝ) / 2) - 1) := by
        calc
          ((1 - u) ^ 2)⁻¹ * (1 - u) ^ (1 / 2 : ℝ) * (1 - u) ^ (((ν : ℝ) + 1) / 2)
            = (1 - u) ^ (-1 : ℝ) * (1 - u) ^ (-1 : ℝ) * (1 - u) ^ (1 / 2 : ℝ) *
                (1 - u) ^ (((ν : ℝ) + 1) / 2) := by
                  rw [pow_two, mul_inv_rev]
                  simp [Real.rpow_neg_one]
          _ = (1 - u) ^ (((ν : ℝ) / 2) - 1) := by
                rw [← Real.rpow_add hu1, ← Real.rpow_add hu1, ← Real.rpow_add hu1]
                congr 1
                ring
      calc
        ((1 - u) ^ 2)⁻¹ *
            (u ^ ((1 / 2 : ℝ) - 1) * (1 - u) ^ (1 / 2 : ℝ) * (1 - u) ^ (((ν : ℝ) + 1) / 2))
          = u ^ ((1 / 2 : ℝ) - 1) *
              (((1 - u) ^ 2)⁻¹ * (1 - u) ^ (1 / 2 : ℝ) * (1 - u) ^ (((ν : ℝ) + 1) / 2)) := by
              ac_rfl
        _ = u ^ ((1 / 2 : ℝ) - 1) * (1 - u) ^ (((ν : ℝ) / 2) - 1) := by
          rw [huPow]
    _ = ProbabilityTheory.beta (1 / 2) ((ν : ℝ) / 2) := by
      apply integral_Ioo_zero_one_betaKernel_eq_beta
      · norm_num
      · positivity

lemma integral_studentTPDFReal_eq_one {ν : ℕ} (hν : 0 < ν) :
    ∫ x, studentTPDFReal ν x = 1 := by
  have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
  let a : ℝ := ((ν : ℝ) + 1) / 2
  have hpow :
      ∫ x in Set.Ioi (0 : ℝ), studentTPDFReal ν x =
        ∫ y in Set.Ioi (0 : ℝ),
          (studentTDensityConstant ν / 2) * y ^ (-(1 / 2 : ℝ)) *
            (1 + y / (ν : ℝ)) ^ (-a) := by
    let g : ℝ → ℝ := fun y =>
      (studentTDensityConstant ν / 2) * y ^ (-(1 / 2 : ℝ)) *
        (1 + y / (ν : ℝ)) ^ (-a)
    have hcomp := MeasureTheory.integral_comp_rpow_Ioi_of_pos (g := g) (p := (2 : ℝ)) zero_lt_two
    calc
      ∫ x in Set.Ioi (0 : ℝ), studentTPDFReal ν x
        = ∫ x in Set.Ioi (0 : ℝ), (2 * x ^ (2 - 1)) • g (x ^ 2) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro x hx
            have hxpos : 0 < x := hx
            have hsquare : (x ^ 2) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
              rw [rpow_neg_half_eq_inv_sqrt (sq_pos_of_pos hxpos), Real.sqrt_sq hxpos.le]
            have hνterm : (↑ν * (↑ν)⁻¹ + x ^ 2 * (↑ν)⁻¹) = 1 + x ^ 2 / (ν : ℝ) := by
              field_simp [hνr.ne']
            have hxterm : x * (x ^ 2) ^ (-(1 / 2 : ℝ)) = 1 := by
              rw [hsquare]
              field_simp [hxpos.ne']
            symm
            calc
              ((fun x => (2 * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ))) x)
                = (2 * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ)) := by
                    rfl
              _ = studentTDensityConstant ν *
                    (↑ν * (↑ν)⁻¹ + x ^ 2 * (↑ν)⁻¹) ^ (-a) := by
                    have hxpow : x ^ ((2 : ℝ) - 1) = x := by
                      rw [show (2 - 1 : ℝ) = (1 : ℝ) by norm_num, Real.rpow_one]
                    have hxterm' : x * (x ^ 2) ^ (-1 / 2 : ℝ) = 1 := by
                      convert hxterm using 1 <;> ring
                    have hνterm0 : 1 + x ^ 2 * (↑ν)⁻¹ = ↑ν * (↑ν)⁻¹ + x ^ 2 * (↑ν)⁻¹ := by
                      field_simp [hνr.ne']
                    have hxterm2 : x * (x ^ 2) ^ (-((2 : ℝ)⁻¹)) = 1 := by
                      convert hxterm using 1 <;> ring
                    have hνterm3 : 1 + x ^ 2 / (ν : ℝ) = ↑ν * (↑ν)⁻¹ + x ^ 2 * (↑ν)⁻¹ := by
                      field_simp [hνr.ne']
                    rw [hxpow]
                    simp [g, smul_eq_mul]
                    calc
                      2 * x *
                          (studentTDensityConstant ν / 2 * (x ^ 2) ^ (-((2 : ℝ)⁻¹)) *
                            (1 + x ^ 2 / (ν : ℝ)) ^ (-a))
                        = studentTDensityConstant ν * (x * (x ^ 2) ^ (-((2 : ℝ)⁻¹))) *
                            (1 + x ^ 2 / (ν : ℝ)) ^ (-a) := by
                              ring_nf
                      _ = studentTDensityConstant ν * (1 + x ^ 2 / (ν : ℝ)) ^ (-a) := by
                            rw [hxterm2]
                            simp
                      _ = studentTDensityConstant ν *
                            (↑ν * (↑ν)⁻¹ + x ^ 2 * (↑ν)⁻¹) ^ (-a) := by
                            rw [hνterm3]
              _ = studentTDensityConstant ν * (1 + x ^ 2 / (ν : ℝ)) ^ (-a) := by
                    rw [hνterm]
              _ = studentTPDFReal ν x := by
                    rw [studentTPDFReal_of_pos hν]
                    congr 2
                    dsimp [a]
                    ring
      _ = ∫ y in Set.Ioi (0 : ℝ), g y := hcomp
  have hscale :
      ∫ y in Set.Ioi (0 : ℝ),
          (studentTDensityConstant ν / 2) * y ^ (-(1 / 2 : ℝ)) * (1 + y / (ν : ℝ)) ^ (-a) =
        ((studentTDensityConstant ν * Real.sqrt (ν : ℝ)) / 2) *
          ∫ z in Set.Ioi (0 : ℝ), z ^ (-(1 / 2 : ℝ)) * (1 + z) ^ (-a) := by
    let g : ℝ → ℝ := fun y =>
      (studentTDensityConstant ν / 2) * y ^ (-(1 / 2 : ℝ)) * (1 + y / (ν : ℝ)) ^ (-a)
    have hbase := MeasureTheory.integral_comp_mul_left_Ioi g (a := (0 : ℝ)) hνr
    rw [smul_eq_mul] at hbase
    have hbase' :
        ∫ y in Set.Ioi (0 : ℝ), g y =
          (ν : ℝ) * ∫ z in Set.Ioi (0 : ℝ), g ((ν : ℝ) * z) := by
      have := congrArg (fun t : ℝ => (ν : ℝ) * t) hbase
      simpa [g, mul_assoc, hνr.ne'] using this.symm
    rw [hbase']
    have hcongr :
        ∫ z in Set.Ioi (0 : ℝ), g ((ν : ℝ) * z) =
          ∫ z in Set.Ioi (0 : ℝ),
            ((studentTDensityConstant ν / 2) * (ν : ℝ) ^ (-(1 / 2 : ℝ))) *
              (z ^ (-(1 / 2 : ℝ)) * (1 + z) ^ (-a)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro z hz
      have hz_nonneg : 0 ≤ z := le_of_lt hz
      simp [g]
      have hmulrpow : (((ν : ℝ) * z) ^ (-((2 : ℝ)⁻¹))) =
          (ν : ℝ) ^ (-((2 : ℝ)⁻¹)) * z ^ (-((2 : ℝ)⁻¹)) := by
        rw [Real.mul_rpow hνr.le hz_nonneg]
      rw [hmulrpow]
      rw [show (1 + ((ν : ℝ) * z) / (ν : ℝ)) = 1 + z by field_simp [hνr.ne']]
      ring_nf
    rw [hcongr, integral_const_mul]
    have hνsqrt : (ν : ℝ) * ((studentTDensityConstant ν / 2) * (ν : ℝ) ^ (-(1 / 2 : ℝ))) =
        (studentTDensityConstant ν * Real.sqrt (ν : ℝ)) / 2 := by
      rw [Real.rpow_neg hνr.le (1 / 2 : ℝ), Real.sqrt_eq_rpow]
      have hsq : (ν : ℝ) = ((ν : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hνr.le]
        norm_num
      have hsqrt_sq : ((((ν : ℝ) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)) = (ν : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        · norm_num
        · positivity
      rw [hsq]
      rw [hsqrt_sq]
      field_simp [Real.sqrt_ne_zero'.2 hνr]
    calc
      (ν : ℝ) *
          (((studentTDensityConstant ν / 2) * (ν : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ z in Set.Ioi (0 : ℝ), z ^ (-(1 / 2 : ℝ)) * (1 + z) ^ (-a))
        = ((ν : ℝ) * ((studentTDensityConstant ν / 2) * (ν : ℝ) ^ (-(1 / 2 : ℝ)))) *
            ∫ z in Set.Ioi (0 : ℝ), z ^ (-(1 / 2 : ℝ)) * (1 + z) ^ (-a) := by ring
      _ = ((studentTDensityConstant ν * Real.sqrt (ν : ℝ)) / 2) *
            ∫ z in Set.Ioi (0 : ℝ), z ^ (-(1 / 2 : ℝ)) * (1 + z) ^ (-a) := by
        rw [hνsqrt]
  calc
    ∫ x, studentTPDFReal ν x
      = 2 * ∫ x in Set.Ioi (0 : ℝ), studentTPDFReal ν x := by
        simpa [studentTPDFReal_abs] using integral_comp_abs (f := studentTPDFReal ν)
    _ = 2 * (((studentTDensityConstant ν * Real.sqrt (ν : ℝ)) / 2) *
          ∫ z in Set.Ioi (0 : ℝ), z ^ (-(1 / 2 : ℝ)) * (1 + z) ^ (-a)) := by
        rw [hpow, hscale]
    _ = 1 := by
      rw [integral_Ioi_studentTKernel_eq_beta hν, studentTDensityConstant_of_pos hν,
        ProbabilityTheory.beta]
      rw [Real.Gamma_one_half_eq]
      have hgamma_arg : (1 / 2 : ℝ) + (ν : ℝ) / 2 = ((ν : ℝ) + 1) / 2 := by ring
      rw [hgamma_arg]
      have hsqrt : Real.sqrt ((ν : ℝ) * Real.pi) = Real.sqrt (ν : ℝ) * Real.sqrt Real.pi := by
        rw [Real.sqrt_mul (show 0 ≤ (ν : ℝ) by positivity)]
      rw [hsqrt]
      field_simp [Real.Gamma_pos_of_pos (by positivity), Real.Gamma_pos_of_pos (by positivity),
        Real.sqrt_ne_zero'.2 hνr, Real.pi_pos.ne']

@[simp]
lemma lintegral_studentTPDF_eq_one {ν : ℕ} (hν : 0 < ν) :
    ∫⁻ x, studentTPDF ν x = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  · unfold studentTPDF
    rw [← integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => studentTPDFReal_nonneg ν x)
      (stronglyMeasurable_studentTPDFReal ν).aestronglyMeasurable, integral_studentTPDFReal_eq_one hν]

lemma integrable_studentTPDFReal {ν : ℕ} (hν : 0 < ν) :
    Integrable (studentTPDFReal ν) := by
  have h_nonneg : 0 ≤ᵐ[volume] studentTPDFReal ν :=
    ae_of_all _ (studentTPDFReal_nonneg ν)
  have h_lintegral :
      ∫⁻ x, ENNReal.ofReal (studentTPDFReal ν x) ∂ volume ≠ ∞ := by
    rw [show ∫⁻ x, ENNReal.ofReal (studentTPDFReal ν x) ∂ volume = 1 by
      simpa [studentTPDF] using (lintegral_studentTPDF_eq_one hν)]
    simp
  exact (lintegral_ofReal_ne_top_iff_integrable
    (stronglyMeasurable_studentTPDFReal ν).aestronglyMeasurable h_nonneg).mp h_lintegral

lemma isProbabilityMeasure_classicalStudentT {ν : ℕ} (hν : 0 < ν) :
    IsProbabilityMeasure (classicalStudentT ν) := by
  refine ⟨?_⟩
  simpa [classicalStudentT] using lintegral_studentTPDF_eq_one hν

lemma classicalStudentT_real_eq_integral {ν : ℕ} (hν : 0 < ν) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (classicalStudentT ν).real s = ∫ x in s, studentTPDFReal ν x := by
  have h_nonneg : 0 ≤ᵐ[volume.restrict s] studentTPDFReal ν :=
    ae_of_all _ (studentTPDFReal_nonneg ν)
  have h_int : IntegrableOn (studentTPDFReal ν) s :=
    (integrable_studentTPDFReal hν).integrableOn
  rw [measureReal_def, classicalStudentT, withDensity_apply _ hs]
  change (∫⁻ x in s, ENNReal.ofReal (studentTPDFReal ν x) ∂volume).toReal =
    ∫ x in s, studentTPDFReal ν x
  rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae h_nonneg)

lemma classicalStudentT_real_Icc_neg_two_two_eq {ν : ℕ} (hν : 0 < ν) :
    (classicalStudentT ν).real (Set.Icc (-2 : ℝ) 2) =
      2 * studentTDensityConstant ν *
        ∫ x in (0 : ℝ)..2, studentTTwoCoverageKernel ν x := by
  let f : ℝ → ℝ := studentTPDFReal ν
  have hf_int : Integrable f := integrable_studentTPDFReal hν
  have hset_interval :
      ∫ x in Set.Icc (-2 : ℝ) 2, f x = ∫ x in (-2 : ℝ)..2, f x := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (f := f) (μ := volume) (by norm_num)]
  have hsplit :
      (∫ x in (-2 : ℝ)..0, f x) + (∫ x in (0 : ℝ)..2, f x) =
        ∫ x in (-2 : ℝ)..2, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf_int.intervalIntegrable : IntervalIntegrable f volume (-2 : ℝ) 0)
      (hf_int.intervalIntegrable : IntervalIntegrable f volume (0 : ℝ) 2)
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f]
    rw [← studentTPDFReal_abs ν (-x), ← studentTPDFReal_abs ν x]
    simp
  have hneg :
      ∫ x in (-2 : ℝ)..0, f x = ∫ x in (0 : ℝ)..2, f x := by
    calc
      ∫ x in (-2 : ℝ)..0, f x
          = ∫ x in (0 : ℝ)..2, f (-x) := by
            simpa using
              (intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := 2)).symm
      _ = ∫ x in (0 : ℝ)..2, f x := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        exact heven x
  have hpos :
      ∫ x in (0 : ℝ)..2, f x =
        studentTDensityConstant ν *
          ∫ x in (0 : ℝ)..2, studentTTwoCoverageKernel ν x := by
    calc
      ∫ x in (0 : ℝ)..2, f x
          = ∫ x in (0 : ℝ)..2,
              studentTDensityConstant ν * studentTTwoCoverageKernel ν x := by
            refine intervalIntegral.integral_congr ?_
            intro x hx
            dsimp [f]
            rw [studentTPDFReal_of_pos hν]
            congr 1
            simp [studentTTwoCoverageKernel]
            ring
      _ = studentTDensityConstant ν *
          ∫ x in (0 : ℝ)..2, studentTTwoCoverageKernel ν x := by
        rw [intervalIntegral.integral_const_mul]
  calc
    (classicalStudentT ν).real (Set.Icc (-2 : ℝ) 2)
        = ∫ x in Set.Icc (-2 : ℝ) 2, f x := by
          simpa [f] using
            classicalStudentT_real_eq_integral (ν := ν) hν (s := Set.Icc (-2 : ℝ) 2)
              measurableSet_Icc
    _ = ∫ x in (-2 : ℝ)..2, f x := hset_interval
    _ = (∫ x in (-2 : ℝ)..0, f x) + (∫ x in (0 : ℝ)..2, f x) := hsplit.symm
    _ = 2 * ∫ x in (0 : ℝ)..2, f x := by
      calc
        (∫ x in (-2 : ℝ)..0, f x) + (∫ x in (0 : ℝ)..2, f x)
            = (∫ x in (0 : ℝ)..2, f x) + (∫ x in (0 : ℝ)..2, f x) := by
              exact congrArg (fun y => y + ∫ x in (0 : ℝ)..2, f x) hneg
        _ = 2 * ∫ x in (0 : ℝ)..2, f x := by ring
    _ = 2 * studentTDensityConstant ν *
        ∫ x in (0 : ℝ)..2, studentTTwoCoverageKernel ν x := by
      rw [hpos]
      ring

lemma studentTTwoCoverageLowerBound_le_classicalStudentT_Icc_neg_two_two
    {ν : ℕ} (hν : 0 < ν) :
    studentTTwoCoverageLowerBound ν ≤ (classicalStudentT ν).real (Set.Icc (-2 : ℝ) 2) := by
  rw [classicalStudentT_real_Icc_neg_two_two_eq hν, studentTTwoCoverageLowerBound]
  exact mul_le_mul_of_nonneg_left (studentTTwoCoverageKernelLowerBound_le_integral_kernel hν)
    (mul_nonneg (by norm_num) (studentTDensityConstant_nonneg ν))

/-- The central Student-t mass on the two-standard-error interval is at least `19/20` once
there are at least 61 degrees of freedom. This is the standalone numerical-probability input for
Hansen's Theorem 5.10. -/
theorem classicalStudentT_Icc_neg_two_two_ge_nineteen_twentieths
    {ν : ℕ} (hν : 61 ≤ ν) :
    (19 : ℝ) / 20 ≤ (classicalStudentT ν).real (Set.Icc (-2 : ℝ) 2) := by
  exact (studentTTwoCoverageLowerBound_ge_nineteen_twentieths_of_ge_sixty_one hν).trans
    (studentTTwoCoverageLowerBound_le_classicalStudentT_Icc_neg_two_two (by omega))

private lemma sqrt_ratio_gaussian_denom {ν : ℕ} {q : ℝ} (hq : 0 < q) :
    Real.sqrt (2 * Real.pi * ((ν : ℝ) / q)) =
      Real.sqrt (2 * Real.pi * (ν : ℝ)) / Real.sqrt q := by
  have hq_ne : q ≠ 0 := hq.ne'
  have hmuldiv : 2 * Real.pi * ((ν : ℝ) / q) = (2 * Real.pi * (ν : ℝ)) / q := by
    field_simp [hq_ne]
  rw [hmuldiv, Real.sqrt_div (by positivity)]

private lemma gaussianPDFReal_ratio_var_eq {ν : ℕ} (hν : 0 < ν) {x q : ℝ} (hq : 0 < q) :
    gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x =
      (Real.sqrt q / Real.sqrt (2 * Real.pi * (ν : ℝ))) *
        Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q)) ) := by
  have hνqnn : 0 ≤ (ν : ℝ) / q := by positivity
  rw [show Real.toNNReal ((ν : ℝ) / q) = ⟨(ν : ℝ) / q, hνqnn⟩ by
    ext
    simp [Real.toNNReal_of_nonneg hνqnn]]
  rw [gaussianPDFReal]
  rw [show (x - 0) ^ 2 = x ^ 2 by ring]
  change
    (Real.sqrt (2 * Real.pi * ((ν : ℝ) / q)))⁻¹ * Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q))) =
      (Real.sqrt q / Real.sqrt (2 * Real.pi * (ν : ℝ))) *
        Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q)))
  rw [sqrt_ratio_gaussian_denom hq]
  field_simp [Real.sqrt_ne_zero'.2 hq,
    Real.sqrt_ne_zero'.2 (by
      have hνr : 0 < (ν : ℝ) := by exact_mod_cast hν
      positivity : 0 < 2 * Real.pi * (ν : ℝ))]

private lemma gammaPDFReal_chiSqKernel_eq {ν : ℕ} {q : ℝ} (hq : 0 < q) :
    gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q =
      (((1 / 2 : ℝ) ^ ((ν : ℝ) / 2)) / Real.Gamma ((ν : ℝ) / 2)) *
        q ^ (((ν : ℝ) / 2) - 1) * Real.exp (-((1 / 2 : ℝ) * q)) := by
  rw [gammaPDFReal, if_pos hq.le]

private lemma studentT_kernel_power_eq {ν : ℕ} {q : ℝ}
    (hq : 0 < q) (a : ℝ) (ha : a = ((ν : ℝ) + 1) / 2) :
    (Real.sqrt q / Real.sqrt (2 * Real.pi * (ν : ℝ))) * q ^ (((ν : ℝ) / 2) - 1) =
      (1 / Real.sqrt (2 * Real.pi * (ν : ℝ))) * q ^ (a - 1) := by
  have hpow0 : Real.sqrt q * q ^ (((ν : ℝ) / 2) - 1) = q ^ (a - 1) := by
    rw [show Real.sqrt q = q ^ (1 / 2 : ℝ) by rw [Real.sqrt_eq_rpow]]
    rw [← Real.rpow_add hq (1 / 2 : ℝ) ((((ν : ℝ) / 2) - 1))]
    congr 1
    rw [ha]
    ring
  calc
    (Real.sqrt q / Real.sqrt (2 * Real.pi * (ν : ℝ))) * q ^ (((ν : ℝ) / 2) - 1)
      = (1 / Real.sqrt (2 * Real.pi * (ν : ℝ))) *
          (Real.sqrt q * q ^ (((ν : ℝ) / 2) - 1)) := by
            ring
    _ = (1 / Real.sqrt (2 * Real.pi * (ν : ℝ))) * q ^ (a - 1) := by rw [hpow0]

private lemma studentT_kernel_exp_eq {ν : ℕ} {x q : ℝ}
    (hν : 0 < ν) (hq : 0 < q) (r : ℝ) (hr : r = (1 + x ^ 2 / (ν : ℝ)) / 2) :
    Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q))) * Real.exp (-((1 / 2 : ℝ) * q)) =
      Real.exp (-(r * q)) := by
  have harg :
      -(x ^ 2) / (2 * ((ν : ℝ) / q)) + -((1 / 2 : ℝ) * q) = -(r * q) := by
    rw [hr]
    have hνr : (ν : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hν)
    field_simp [hq.ne', hνr]
    ring
  rw [← Real.exp_add, harg]

private lemma integral_Ioi_ratio_kernel_eq_studentTPDFReal {ν : ℕ}
    (hν : 0 < ν) (x : ℝ) :
    ∫ q in Set.Ioi (0 : ℝ),
      gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
        gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q =
      studentTPDFReal ν x := by
  have hνr : 0 < (ν : ℝ) := by
    exact_mod_cast hν
  let a : ℝ := ((ν : ℝ) + 1) / 2
  let r : ℝ := (1 + x ^ 2 / (ν : ℝ)) / 2
  let C : ℝ :=
    (1 / Real.sqrt (2 * Real.pi * (ν : ℝ))) *
      (((1 / 2 : ℝ) ^ ((ν : ℝ) / 2)) / Real.Gamma ((ν : ℝ) / 2))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  calc
    ∫ q in Set.Ioi (0 : ℝ),
        gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
          gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q
      = ∫ q in Set.Ioi (0 : ℝ),
          C * (q ^ (a - 1) * Real.exp (-(r * q))) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro q hq
            dsimp
            rw [gaussianPDFReal_ratio_var_eq hν hq, gammaPDFReal_chiSqKernel_eq hq]
            have hpow :
                Real.sqrt q * q ^ (((ν : ℝ) / 2) - 1) = q ^ (a - 1) := by
              rw [show Real.sqrt q = q ^ (1 / 2 : ℝ) by rw [Real.sqrt_eq_rpow]]
              rw [← Real.rpow_add hq (1 / 2 : ℝ) ((((ν : ℝ) / 2) - 1))]
              congr 1
              rw [show a = ((ν : ℝ) + 1) / 2 by rfl]
              ring
            have hexp :=
              studentT_kernel_exp_eq hν hq r rfl
            calc
              (Real.sqrt q / Real.sqrt (2 * Real.pi * (ν : ℝ)) *
                  Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q)))) *
                  ((((1 / 2 : ℝ) ^ ((ν : ℝ) / 2)) / Real.Gamma ((ν : ℝ) / 2)) *
                    q ^ (((ν : ℝ) / 2) - 1) * Real.exp (-((1 / 2 : ℝ) * q)))
                =
                  C *
                    (Real.sqrt q * q ^ (((ν : ℝ) / 2) - 1)) *
                    (Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q))) *
                      Real.exp (-((1 / 2 : ℝ) * q))) := by
                    dsimp [C]
                    ring_nf
              _ =
                  C * q ^ (a - 1) *
                    (Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q))) *
                      Real.exp (-((1 / 2 : ℝ) * q))) := by
                    rw [hpow]
              _ =
                  C * (q ^ (a - 1) * Real.exp (-(r * q))) := by
                    rw [hexp]
                    ring
    _ =
        C * ((1 / r) ^ a * Real.Gamma a) := by
          have hI :
              ∫ q in Set.Ioi (0 : ℝ), C * (q ^ (a - 1) * Real.exp (-(r * q))) =
                C * ∫ q in Set.Ioi (0 : ℝ), q ^ (a - 1) * Real.exp (-(r * q)) := by
            rw [integral_const_mul]
          rw [hI]
          congr 1
          exact Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
    _ = studentTPDFReal ν x := by
      rw [studentTPDFReal_of_pos hν, studentTDensityConstant_of_pos hν]
      have hbase_nonneg : 0 ≤ 1 + x ^ 2 / (ν : ℝ) := by
        positivity
      have hpowtwo :
          (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ ((ν : ℝ) / 2) = Real.sqrt 2 := by
        rw [show (1 / 2 : ℝ) ^ ((ν : ℝ) / 2) = (2 : ℝ) ^ (-((ν : ℝ) / 2)) by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
          rw [← Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]]
        rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ)) a (-((ν : ℝ) / 2))]
        rw [show a + -((ν : ℝ) / 2) = (1 / 2 : ℝ) by
          dsimp [a]
          ring]
        rw [Real.sqrt_eq_rpow]
      have hrpow :
          (1 / r) ^ a = (2 : ℝ) ^ a * (1 + x ^ 2 / (ν : ℝ)) ^ (-a) := by
        rw [show 1 / r = 2 / (1 + x ^ 2 / (ν : ℝ)) by
          dsimp [r]
          field_simp [hνr.ne']]
        rw [Real.div_rpow (by norm_num : 0 ≤ (2 : ℝ)) hbase_nonneg]
        rw [Real.rpow_neg hbase_nonneg]
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      have hsqrt :
          Real.sqrt (2 * Real.pi * (ν : ℝ)) =
            Real.sqrt 2 * Real.sqrt (Real.pi * (ν : ℝ)) := by
        rw [show 2 * Real.pi * (ν : ℝ) = 2 * (Real.pi * (ν : ℝ)) by ring]
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
      rw [hrpow]
      have hrew :
          C * ((2 : ℝ) ^ a * (1 + x ^ 2 / (ν : ℝ)) ^ (-a) * Real.Gamma a) =
            (((1 / Real.sqrt (2 * Real.pi * (ν : ℝ))) *
              ((2 : ℝ) ^ a * (1 / 2 : ℝ) ^ ((ν : ℝ) / 2))) *
              (Real.Gamma a / Real.Gamma ((ν : ℝ) / 2))) *
              (1 + x ^ 2 / (ν : ℝ)) ^ (-a) := by
        dsimp [C]
        ring_nf
      rw [hrew, hpowtwo, hsqrt]
      have hsqrtcancel :
          (1 / (Real.sqrt 2 * Real.sqrt (Real.pi * (ν : ℝ))) * Real.sqrt 2) =
            1 / Real.sqrt (Real.pi * (ν : ℝ)) := by
        field_simp [Real.sqrt_ne_zero'.2 (by positivity : 0 < (2 : ℝ)),
          Real.sqrt_ne_zero'.2 (by positivity : 0 < Real.pi * (ν : ℝ))]
      rw [hsqrtcancel, show a = ((ν : ℝ) + 1) / 2 by rfl]
      rw [show Real.sqrt (Real.pi * (ν : ℝ)) = Real.sqrt ((ν : ℝ) * Real.pi) by rw [mul_comm]]
      ring

private lemma integrableOn_Ioi_ratio_kernel {ν : ℕ} (hν : 0 < ν) (x : ℝ) :
    IntegrableOn
      (fun q =>
        gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
          gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q)
      (Set.Ioi (0 : ℝ)) := by
  have hνr : 0 < (ν : ℝ) := by
    exact_mod_cast hν
  let a : ℝ := ((ν : ℝ) + 1) / 2
  let r : ℝ := (1 + x ^ 2 / (ν : ℝ)) / 2
  let C : ℝ :=
    (1 / Real.sqrt (2 * Real.pi * (ν : ℝ))) *
      (((1 / 2 : ℝ) ^ ((ν : ℝ) / 2)) / Real.Gamma ((ν : ℝ) / 2))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hbase0 :
      IntegrableOn (fun q : ℝ => q ^ (a - 1) * Real.exp (-(r * q))) (Set.Ioi (0 : ℝ)) := by
    simpa using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (show -1 < a - 1 by linarith) (by norm_num : (1 : ℝ) ≤ 1) hr)
  have hbase :
      IntegrableOn (fun q : ℝ => C * (q ^ (a - 1) * Real.exp (-(r * q)))) (Set.Ioi (0 : ℝ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase0.const_mul C
  refine IntegrableOn.congr_fun hbase ?_ measurableSet_Ioi
  intro q hq
  dsimp [C]
  rw [gaussianPDFReal_ratio_var_eq hν hq, gammaPDFReal_chiSqKernel_eq hq]
  have hpow :
      Real.sqrt q * q ^ (((ν : ℝ) / 2) - 1) = q ^ (a - 1) := by
    rw [show Real.sqrt q = q ^ (1 / 2 : ℝ) by rw [Real.sqrt_eq_rpow]]
    rw [← Real.rpow_add hq (1 / 2 : ℝ) ((((ν : ℝ) / 2) - 1))]
    congr 1
    rw [show a = ((ν : ℝ) + 1) / 2 by rfl]
    ring
  have hexp := studentT_kernel_exp_eq hν hq r rfl
  have hk :
      (Real.sqrt q / Real.sqrt (2 * Real.pi * (ν : ℝ)) *
          Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q)))) *
          ((((1 / 2 : ℝ) ^ ((ν : ℝ) / 2)) / Real.Gamma ((ν : ℝ) / 2)) *
            q ^ (((ν : ℝ) / 2) - 1) * Real.exp (-((1 / 2 : ℝ) * q)))
        = C * (q ^ (a - 1) * Real.exp (-(r * q))) := by
    calc
      (Real.sqrt q / Real.sqrt (2 * Real.pi * (ν : ℝ)) *
          Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q)))) *
          ((((1 / 2 : ℝ) ^ ((ν : ℝ) / 2)) / Real.Gamma ((ν : ℝ) / 2)) *
            q ^ (((ν : ℝ) / 2) - 1) * Real.exp (-((1 / 2 : ℝ) * q)))
        =
          C *
            (Real.sqrt q * q ^ (((ν : ℝ) / 2) - 1)) *
            (Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q))) *
              Real.exp (-((1 / 2 : ℝ) * q))) := by
                dsimp [C]
                ring_nf
      _ =
          C * q ^ (a - 1) *
            (Real.exp (-(x ^ 2) / (2 * ((ν : ℝ) / q))) *
              Real.exp (-((1 / 2 : ℝ) * q))) := by
                rw [hpow]
      _ = C * (q ^ (a - 1) * Real.exp (-(r * q))) := by
            rw [hexp]
            ring
  dsimp [C] at hk ⊢
  exact hk.symm

private lemma lintegral_Ioi_ratio_kernel_eq_studentTPDF {ν : ℕ}
    (hν : 0 < ν) (x : ℝ) :
    ∫⁻ q in Set.Ioi (0 : ℝ),
      ENNReal.ofReal
        (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
          gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q) =
      ENNReal.ofReal (studentTPDFReal ν x) := by
  have h_int :
      Integrable
        (fun q =>
          gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
            gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_Ioi_ratio_kernel hν x
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun q =>
        gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
          gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q := by
    have hνr : 0 < (ν : ℝ) := by
      exact_mod_cast hν
    exact ae_of_all _ fun q =>
      mul_nonneg (gaussianPDFReal_nonneg 0 _ _) (gammaPDFReal_nonneg (by positivity) (by positivity) q)
  rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  simpa using congrArg ENNReal.ofReal (integral_Ioi_ratio_kernel_eq_studentTPDFReal hν x)

private lemma lintegral_ratio_kernel_eq_studentTPDF {ν : ℕ}
    (hν : 0 < ν) (x : ℝ) :
    ∫⁻ q,
      gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
        ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x) ∂ volume =
      ENNReal.ofReal (studentTPDFReal ν x) := by
  have hq0_ae : ∀ᵐ q : ℝ ∂ volume, q ≠ 0 := by
    have hnotmem : ∀ᵐ q : ℝ ∂ volume, q ∉ ({0} : Set ℝ) :=
      (measure_eq_zero_iff_ae_notMem.1 (by simp))
    simpa using hnotmem
  have hcongr :
      (fun q =>
        gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
          ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x))
        =ᵐ[volume]
      Set.indicator (Set.Ioi (0 : ℝ)) (fun q =>
        ENNReal.ofReal
          (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
            gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q)) := by
    filter_upwards [hq0_ae] with q hq0
    by_cases hq : 0 < q
    · rw [gammaPDF_of_nonneg hq.le]
      have hgamma_nonneg : 0 ≤ gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q :=
        gammaPDFReal_nonneg (by positivity) (by positivity) q
      have hexp_nonneg :
          0 ≤ (1 / 2 : ℝ) ^ ((ν : ℝ) / 2) / Real.Gamma ((ν : ℝ) / 2) *
            q ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(1 / 2 * q)) := by
        simpa [gammaPDFReal, hq.le] using hgamma_nonneg
      calc
        ENNReal.ofReal
            ((1 / 2 : ℝ) ^ ((ν : ℝ) / 2) / Real.Gamma ((ν : ℝ) / 2) *
              q ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(1 / 2 * q))) *
            ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x)
          = ENNReal.ofReal
              (((1 / 2 : ℝ) ^ ((ν : ℝ) / 2) / Real.Gamma ((ν : ℝ) / 2) *
                  q ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(1 / 2 * q))) *
                gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x) := by
              have hmul :
                  ENNReal.ofReal
                    ((((1 / 2 : ℝ) ^ ((ν : ℝ) / 2) / Real.Gamma ((ν : ℝ) / 2) *
                        q ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(1 / 2 * q))) *
                      gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x)) =
                    ENNReal.ofReal
                      (((1 / 2 : ℝ) ^ ((ν : ℝ) / 2) / Real.Gamma ((ν : ℝ) / 2) *
                          q ^ ((ν : ℝ) / 2 - 1) * Real.exp (-(1 / 2 * q)))) *
                      ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x) :=
                ENNReal.ofReal_mul hexp_nonneg
              simpa using hmul.symm
        _ = ENNReal.ofReal
              (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
                gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q) := by
              simp [gammaPDFReal, hq.le, mul_assoc, mul_left_comm, mul_comm]
        _ = (Set.Ioi (0 : ℝ)).indicator
              (fun q =>
                ENNReal.ofReal
                  (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x *
                    gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ) q)) q := by
              simp [Set.indicator, hq]
    · have hqneg : q < 0 := lt_of_le_of_ne (le_of_not_gt hq) hq0
      simp [Set.indicator, hq, gammaPDF_of_neg hqneg]
  rw [lintegral_congr_ae hcongr, lintegral_indicator measurableSet_Ioi]
  exact lintegral_Ioi_ratio_kernel_eq_studentTPDF hν x

/-- The one-dimensional factor multiplying the Gaussian numerator in the classical ratio
representation of Student's `t` distribution. -/
noncomputable def studentTFactor (ν : ℕ) : Measure ℝ :=
  (chiSquared ν).map fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q

/-- Student's `t` distribution, packaged as the law of the product
`Z * (√ν / √Q)` with `Z ∼ N(0,1)` and `Q ∼ χ²(ν)` independent. This lives in a standalone module
so later work can connect it to the classical density / cdf formulas without leaving the Chapter 5
theorems self-referential. -/
noncomputable def studentT (ν : ℕ) : Measure ℝ :=
  gaussianReal 0 1 ∗ₘ studentTFactor ν

lemma isProbabilityMeasure_studentTFactor {ν : ℕ} (hν : 0 < ν) :
    IsProbabilityMeasure (studentTFactor ν) := by
  haveI : IsProbabilityMeasure (chiSquared ν) := isProbabilityMeasure_chiSquared hν
  change IsProbabilityMeasure ((chiSquared ν).map fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma isProbabilityMeasure_studentT {ν : ℕ} (hν : 0 < ν) :
    IsProbabilityMeasure (studentT ν) := by
  haveI : IsProbabilityMeasure (studentTFactor ν) := isProbabilityMeasure_studentTFactor hν
  dsimp [studentT]
  infer_instance

lemma studentT_eq_map_ratio_prod {ν : ℕ} (hν : 0 < ν) :
    studentT ν =
      ((gaussianReal 0 1).prod (chiSquared ν)).map
        (fun p : ℝ × ℝ => p.1 * (Real.sqrt (ν : ℝ) / Real.sqrt p.2)) := by
  letI : IsProbabilityMeasure (chiSquared ν) := isProbabilityMeasure_chiSquared hν
  have hfac : Measurable (fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q) := by
    fun_prop
  unfold studentT studentTFactor Measure.mconv
  have hprod :
      (gaussianReal 0 1).prod (Measure.map (fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
        (chiSquared ν)) =
        Measure.map
          (Prod.map id (fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q))
          ((gaussianReal 0 1).prod (chiSquared ν)) := by
    simpa using
      (Measure.map_prod_map (gaussianReal 0 1) (chiSquared ν) measurable_id hfac)
  rw [hprod]
  simpa [Function.comp] using
    (Measure.map_map
      (μ := (gaussianReal 0 1).prod (chiSquared ν))
      (f := Prod.map id (fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q))
      (g := fun x : ℝ × ℝ => x.1 * x.2)
      (by fun_prop) (by fun_prop))

private lemma lintegral_gaussian_scaled_eq_ratio_pdf {ν : ℕ} (hν : 0 < ν)
    {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ z, φ (z * (Real.sqrt (ν : ℝ) / Real.sqrt q)) ∂ gaussianReal 0 1 =
      ∫⁻ x, φ x * ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x) := by
  have hq_ne : q ≠ 0 := hq.ne'
  have hνr : 0 < (ν : ℝ) := by
    exact_mod_cast hν
  let c : ℝ := Real.sqrt (ν : ℝ) / Real.sqrt q
  let v : ℝ≥0 := ⟨c ^ 2, sq_nonneg _⟩
  have hdiv : 0 < (ν : ℝ) / q := by
    positivity
  have hvar : v = Real.toNNReal ((ν : ℝ) / q) := by
    apply NNReal.eq
    dsimp [v, c]
    rw [max_eq_left hdiv.le]
    field_simp [hq_ne]
    rw [Real.sq_sqrt hq.le, Real.sq_sqrt hνr.le]
    ring
  have hv : (Real.toNNReal ((ν : ℝ) / q) : ℝ≥0) ≠ 0 := by
    rw [← NNReal.coe_ne_zero, Real.toNNReal_of_nonneg hdiv.le]
    exact hdiv.ne'
  calc
    ∫⁻ z, φ (z * (Real.sqrt (ν : ℝ) / Real.sqrt q)) ∂ gaussianReal 0 1
      = ∫⁻ x, φ x ∂
          ((gaussianReal 0 1).map (fun z : ℝ => z * (Real.sqrt (ν : ℝ) / Real.sqrt q))) := by
            rw [lintegral_map' hφ.aemeasurable (by fun_prop)]
    _ = ∫⁻ x, φ x ∂
          gaussianReal (c * 0) (v * 1) := by
          dsimp [c, v]
          rw [gaussianReal_map_mul_const]
    _ = ∫⁻ x, φ x ∂ gaussianReal 0 (Real.toNNReal ((ν : ℝ) / q)) := by
          simp [hvar]
    _ = ∫⁻ x, φ x ∂
          volume.withDensity
            (fun x => ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x)) := by
          rw [gaussianReal_of_var_ne_zero 0 hv]
          rfl
    _ = ∫⁻ x, φ x * ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x) := by
          rw [lintegral_withDensity_eq_lintegral_mul₀
            (hf := by
              exact (by fun_prop : AEMeasurable
                (fun x => ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x))
                volume))
            (hg := hφ.aemeasurable)]
          simpa [Pi.mul_apply, mul_comm]

private lemma measurable_ratio_gaussian_kernel_fixed {ν : ℕ} (x : ℝ) :
    Measurable (fun q : ℝ =>
      ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x)) := by
  simp only [gaussianPDFReal]
  fun_prop

private lemma measurable_ratio_gaussian_kernel {ν : ℕ} :
    Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / z.1)) z.2)) := by
  simp only [gaussianPDFReal]
  fun_prop

private lemma ae_ratio_outer_eq {ν : ℕ} (hν : 0 < ν) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    (fun q =>
      gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
        ∫⁻ z, φ (z * (Real.sqrt (ν : ℝ) / Real.sqrt q)) ∂ gaussianReal 0 1)
      =ᵐ[volume]
    (fun q =>
      ∫⁻ x, gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
        (φ x * ENNReal.ofReal
          (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x)) ∂ volume) := by
  have hq0_ae : ∀ᵐ q : ℝ ∂ volume, q ≠ 0 := by
    have hnotmem : ∀ᵐ q : ℝ ∂ volume, q ∉ ({0} : Set ℝ) :=
      (measure_eq_zero_iff_ae_notMem.1 (by simp))
    simpa using hnotmem
  filter_upwards [hq0_ae] with q hq0
  rcases lt_or_gt_of_ne hq0 with hqneg | hqpos
  · have hgamma : gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q = 0 := gammaPDF_of_neg hqneg
    rw [hgamma]
    simp
  · rw [lintegral_gaussian_scaled_eq_ratio_pdf hν hqpos hφ]
    have hmeas :
        AEMeasurable
          (fun x =>
            φ x * ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x))
          volume :=
        hφ.aemeasurable.mul
          ((measurable_gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q))).ennreal_ofReal.aemeasurable)
    have hconst :=
      lintegral_const_mul'' (gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q) hmeas
    rw [← hconst]

private lemma lintegral_ratio_double_eq {ν : ℕ} (hν : 0 < ν) {φ : ℝ → ℝ≥0∞}
    (hφ : Measurable φ) :
    ∫⁻ q, ∫⁻ x,
      gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
        (φ x * ENNReal.ofReal
          (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x)) ∂ volume ∂ volume =
      ∫⁻ x, φ x * ENNReal.ofReal (studentTPDFReal ν x) ∂ volume := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun q x =>
    gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
      (φ x * ENNReal.ofReal
        (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x))
  let G : ℝ × ℝ → ℝ≥0∞ := fun z => F z.1 z.2
  have hG : Measurable G := by
    dsimp [G, F]
    exact ((measurable_gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ)).comp measurable_fst).mul
      ((hφ.comp measurable_snd).mul measurable_ratio_gaussian_kernel)
  calc
    ∫⁻ q, ∫⁻ x, F q x ∂ volume ∂ volume
      = ∫⁻ z, G z ∂ volume.prod volume := by
          rw [lintegral_lintegral
            (hf := by
              simpa [G, F] using hG.aemeasurable)]
    _ = ∫⁻ x, ∫⁻ q, G (q, x) ∂ volume ∂ volume := by
          rw [lintegral_prod_symm' _ hG]
    _ = ∫⁻ x, φ x * ENNReal.ofReal (studentTPDFReal ν x) ∂ volume := by
          refine lintegral_congr_ae (ae_of_all _ ?_)
          intro x
          have hinner : ∫⁻ q, F q x ∂ volume = φ x * ENNReal.ofReal (studentTPDFReal ν x) := by
            calc
              ∫⁻ q, F q x ∂ volume
                = ∫⁻ q,
                    φ x *
                      (gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
                        ENNReal.ofReal
                          (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x)) ∂ volume := by
                    refine lintegral_congr_ae (ae_of_all _ fun q => ?_)
                    simp [F, mul_assoc, mul_left_comm, mul_comm]
              _ =
                  φ x *
                    ∫⁻ q,
                      gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
                        ENNReal.ofReal
                          (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x) ∂ volume := by
                    have hgauss := measurable_ratio_gaussian_kernel_fixed (ν := ν) x
                    have hmeas :
                        AEMeasurable
                          (fun q =>
                            gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
                              ENNReal.ofReal
                                (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x))
                          volume :=
                        ((measurable_gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ)).aemeasurable).mul
                          hgauss.aemeasurable
                    simpa using (lintegral_const_mul'' (φ x) hmeas)
              _ = φ x * ENNReal.ofReal (studentTPDFReal ν x) := by
                    rw [lintegral_ratio_kernel_eq_studentTPDF hν x]
          simpa [G, F] using hinner

theorem ratio_prod_map_eq_classicalStudentT {ν : ℕ} (hν : 0 < ν) :
    ((gaussianReal 0 1).prod (chiSquared ν)).map
      (fun p : ℝ × ℝ => p.1 * (Real.sqrt (ν : ℝ) / Real.sqrt p.2)) =
    classicalStudentT ν := by
  -- Bridge strategy:
  -- 1. View `Z / √(Q/ν)` as a measurable map of the product law `N(0,1) × χ²_ν`.
  -- 2. Integrate first against the chi-square kernel to recover the classical Student-t density.
  -- 3. Conclude equality of measures by extensionality on lintegrals.
  refine Measure.ext_of_lintegral _ ?_
  intro φ hφ
  let ratio : ℝ × ℝ → ℝ := fun p => p.1 * (Real.sqrt (ν : ℝ) / Real.sqrt p.2)
  have hratio : Measurable ratio := by
    dsimp [ratio]
    fun_prop
  rw [lintegral_map' hφ.aemeasurable hratio.aemeasurable]
  rw [chiSquared_eq, gammaMeasure]
  rw [lintegral_prod_symm _ (by
    dsimp [ratio]
    fun_prop)]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀
    (hf := by
      simpa [gammaPDF] using
        (measurable_gammaPDFReal ((ν : ℝ) / 2) (1 / 2 : ℝ)).ennreal_ofReal.aemeasurable)
    (h'f := ae_of_all _ fun q : ℝ => by simp [gammaPDF])]
  have houter :
      (fun q =>
        (gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) *
          fun y => ∫⁻ x, φ (ratio (x, y)) ∂ gaussianReal 0 1) q)
        =ᵐ[volume]
      (fun q =>
        ∫⁻ x, gammaPDF ((ν : ℝ) / 2) (1 / 2 : ℝ) q *
          (φ x * ENNReal.ofReal
            (gaussianPDFReal 0 (Real.toNNReal ((ν : ℝ) / q)) x)) ∂ volume) := by
    simpa [Pi.mul_apply, ratio] using (ae_ratio_outer_eq hν hφ)
  rw [lintegral_congr_ae houter]
  rw [lintegral_ratio_double_eq hν hφ]
  rw [classicalStudentT, lintegral_withDensity_eq_lintegral_mul₀
    (hf := (measurable_studentTPDF ν).aemeasurable) (hg := hφ.aemeasurable)]
  simp [studentTPDF, mul_comm, mul_left_comm, mul_assoc]

theorem studentT_eq_classicalStudentT {ν : ℕ} (hν : 0 < ν) :
    studentT ν = classicalStudentT ν := by
  rw [studentT_eq_map_ratio_prod hν, ratio_prod_map_eq_classicalStudentT hν]

/-- The classical ratio `Z / √(Q/ν)` has the standalone `studentT ν` law whenever
`Z ∼ N(0,1)`, `Q ∼ χ²(ν)`, and `Z` is independent of `Q`. -/
theorem hasLaw_ratio_standardNormal_chiSquared_studentT
    {ν : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z Q : Ω → ℝ}
    (hν : 0 < ν)
    (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hQ : HasLaw Q (chiSquared ν) μ)
    (hInd : Z ⟂ᵢ[μ] Q) :
    HasLaw (fun ω => Z ω * (Real.sqrt (ν : ℝ) / Real.sqrt (Q ω))) (studentT ν) μ := by
  letI : IsProbabilityMeasure (chiSquared ν) := isProbabilityMeasure_chiSquared hν
  letI : IsProbabilityMeasure (studentTFactor ν) := isProbabilityMeasure_studentTFactor hν
  have hMap :
      HasLaw (fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
        (studentTFactor ν) (chiSquared ν) := by
    exact ⟨by fun_prop, rfl⟩
  have hFac : HasLaw (fun ω => Real.sqrt (ν : ℝ) / Real.sqrt (Q ω)) (studentTFactor ν) μ :=
    hMap.comp hQ
  have hIndFac :
      Z ⟂ᵢ[μ] (fun ω => Real.sqrt (ν : ℝ) / Real.sqrt (Q ω)) := by
    refine (IndepFun.comp (φ := id) (ψ := fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
      hInd measurable_id (by fun_prop)).congr ?_ ?_
    · exact Filter.Eventually.of_forall fun _ => rfl
    · exact Filter.Eventually.of_forall fun _ => rfl
  simpa [studentT] using IndepFun.hasLaw_fun_mul hZ hFac hIndFac

end HansenEconometrics
