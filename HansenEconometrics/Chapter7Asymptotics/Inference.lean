import HansenEconometrics.Chapter7Asymptotics.Normality

/-!
# Chapter 7 Asymptotics: Inference

This file contains the Chapter 7 scalar-inference layer:

* generic standard-error positivity and symmetric confidence-interval coverage;
* scalar t-statistic convergence for homoskedastic and robust estimators;
* scalar Wald-to-chi-square wrappers;
* ordinary-wrapper consequences for the textbook-facing `olsBetaOrZero` API.
-/

open scoped Matrix Real

namespace HansenEconometrics

open Matrix

section Assumption72

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology ProbabilityTheory ENNReal symmDiff

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst :
    MeasurableSpace (Matrix k k ℝ) :=
  matrixBorelMeasurableSpace k k

attribute [local instance] matrixBorelMeasurableSpaceInst

omit [DecidableEq k] in
private lemma matrixBorelSpaceInst : BorelSpace (Matrix k k ℝ) :=
  matrixBorelSpace k k

attribute [local instance] matrixBorelSpaceInst

/-- The absolute standard-normal law has no atom at the frontier of `(-∞, c]`. -/
theorem standardNormalAbs_frontier_Iic_null (crit : ℝ) :
    ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (frontier (Set.Iic crit)) = 0 := by
  rw [frontier_Iic]
  rw [Measure.map_apply continuous_abs.measurable (measurableSet_singleton crit)]
  have hpre_subset :
      (fun x : ℝ => |x|) ⁻¹' ({crit} : Set ℝ) ⊆
        ({crit} ∪ {-crit} : Set ℝ) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [Set.mem_union, Set.mem_singleton_iff]
    by_cases hx_nonneg : 0 ≤ x
    · left
      simpa [abs_of_nonneg hx_nonneg] using hx
    · right
      have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hneg : -x = crit := by
        simpa [abs_of_neg hx_neg] using hx
      linarith
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  exact measure_mono_null hpre_subset
    (measure_union_null (measure_singleton crit) (measure_singleton (-crit)))

/-- Squaring a standard-normal distributional limit gives a `χ²(1)` limit. -/
theorem tendstoInDistribution_sq_standardNormal_chiSquared_one
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {T : ℕ → Ω → ℝ}
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1)) :
    TendstoInDistribution (fun n ω => (T n ω) ^ 2) atTop
      (fun x : ℝ => x) P (chiSquared 1) := by
  have hsquare := hT.continuous_comp (by fun_prop : Continuous (fun x : ℝ => x ^ 2))
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def] using hsquare.forall_aemeasurable
  · fun_prop
  · convert hsquare.tendsto using 2
    · ext s hs
      simp [Function.comp_def, gaussianReal_map_sq_eq_chiSquared_one]

omit [DecidableEq k] in
/-- One-row linear maps turn scaled parameter errors into scaled scalar errors.

This is the algebraic bridge between the existing t-statistic numerator
`√n • R(β̂-β)` and the confidence-interval expression `√n(θ̂-θ)`. -/
theorem linearMapUnit_smul_sub_dot_one
    (R : Matrix Unit k ℝ) (b β : k → ℝ) (root : ℝ) :
    (root • (R *ᵥ (b - β))) ⬝ᵥ (fun _ : Unit => 1) =
      root * (((R *ᵥ b) ⬝ᵥ (fun _ : Unit => 1)) -
        ((R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1))) := by
  rw [Matrix.mulVec_sub, smul_dotProduct, sub_dotProduct]
  simp [smul_eq_mul]

omit [DecidableEq k] in
/-- Scalar value of a fixed one-row linear restriction. -/
@[reducible]
noncomputable def linearRestrictionEstimate
    (R : Matrix Unit k ℝ) (b : k → ℝ) : ℝ :=
  (R *ᵥ b) ⬝ᵥ (fun _ : Unit => 1)

omit [DecidableEq k] in
/-- Standard error induced by a covariance estimator for a fixed one-row restriction. -/
@[reducible]
noncomputable def linearRestrictionStdError
    (R : Matrix Unit k ℝ) (Vhat : Matrix k k ℝ) : ℝ :=
  Real.sqrt ((R * Vhat * Rᵀ) () ())

/-- Scalar t-statistic for a generic nonlinear scalar parameter transform. -/
@[reducible]
noncomputable def scalarFunctionTStat
    (θhat θ se root : ℝ) : ℝ :=
  root * (θhat - θ) / se

/-- Symmetric confidence-interval membership for a generic nonlinear scalar parameter transform. -/
@[reducible]
noncomputable def scalarFunctionCIEvent
    (θhat θ se root crit : ℝ) : Prop :=
  θ ∈ Set.Icc
    (θhat - crit * se / root)
    (θhat + crit * se / root)

omit [Fintype k] [DecidableEq k] in
/-- Real-valued CDF of a scalar statistic at a fixed sample size and cutoff. -/
noncomputable def statisticCDFReal
    (μ : Measure Ω) (T : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  μ.real {ω | T n ω ≤ x}

omit [Fintype k] [DecidableEq k] in
/-- First-order Edgeworth expansion interface for scalar statistics.

The field records the theorem-facing content of Hansen's Edgeworth statement:
after multiplying the CDF error by `√n`, the error converges to a fixed
correction function. The concrete polynomial/cumulant calculation that proves
this hypothesis is intentionally left outside this generic wrapper. -/
structure FirstOrderEdgeworthExpansion
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ → Ω → ℝ) (baseCDF correction : ℝ → ℝ) where
  /-- Scaled CDF error converges pointwise to the first Edgeworth correction. -/
  scaled_cdf_error_tendsto :
    ∀ x, Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ) * (statisticCDFReal μ T n x - baseCDF x))
      atTop (𝓝 (correction x))

namespace FirstOrderEdgeworthExpansion

omit [Fintype k] [DecidableEq k] in
/-- First-order Edgeworth expansion, written as a vanishing scaled remainder. -/
theorem scaled_remainder_tendsto_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF correction : ℝ → ℝ}
    (h : FirstOrderEdgeworthExpansion μ T baseCDF correction) (x : ℝ) :
    Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ) *
        (statisticCDFReal μ T n x - baseCDF x -
          (Real.sqrt (n : ℝ))⁻¹ * correction x))
      atTop (𝓝 0) := by
  have hscaled : Tendsto
      (fun n : ℕ =>
        Real.sqrt (n : ℝ) * (statisticCDFReal μ T n x - baseCDF x) -
          correction x)
      atTop (𝓝 0) := by
    simpa using
      (h.scaled_cdf_error_tendsto x).sub
        (tendsto_const_nhds (x := correction x))
  have heq :
      (fun n : ℕ => Real.sqrt (n : ℝ) *
        (statisticCDFReal μ T n x - baseCDF x -
          (Real.sqrt (n : ℝ))⁻¹ * correction x)) =ᶠ[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ) *
        (statisticCDFReal μ T n x - baseCDF x) - correction x) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hnpos
    field_simp [hsqrt_ne]
  rw [tendsto_congr' heq]
  simpa using hscaled

omit [Fintype k] [DecidableEq k] in
/-- A first-order Edgeworth expansion implies ordinary CDF convergence to the base CDF. -/
theorem cdf_tendsto_base
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF correction : ℝ → ℝ}
    (h : FirstOrderEdgeworthExpansion μ T baseCDF correction) (x : ℝ) :
    Tendsto (fun n : ℕ => statisticCDFReal μ T n x) atTop (𝓝 (baseCDF x)) := by
  have hinv_sqrt : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
      atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hprod := hinv_sqrt.mul (h.scaled_cdf_error_tendsto x)
  have herror : Tendsto (fun n : ℕ => statisticCDFReal μ T n x - baseCDF x)
      atTop (𝓝 0) := by
    have heq :
        (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ *
          (Real.sqrt (n : ℝ) *
            (statisticCDFReal μ T n x - baseCDF x))) =ᶠ[atTop]
        (fun n : ℕ => statisticCDFReal μ T n x - baseCDF x) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr hnpos
      field_simp [hsqrt_ne]
    rw [← tendsto_congr' heq]
    simpa using hprod
  have hsum : Tendsto
      (fun n : ℕ => (statisticCDFReal μ T n x - baseCDF x) + baseCDF x)
      atTop (𝓝 (0 + baseCDF x)) :=
    herror.add (tendsto_const_nhds (x := baseCDF x))
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum

end FirstOrderEdgeworthExpansion

omit [Fintype k] [DecidableEq k] in
/-- Second-order uniform Edgeworth expansion interface for scalar statistics.

This is the theorem-facing shape of Hansen Theorem 7.15: the CDF of a scalar
statistic is approximated uniformly in the cutoff `x` by a base CDF plus
`n^{-1/2}` and `n^{-1}` correction terms. For the textbook t-ratio application,
`baseCDF` is the standard-normal CDF, `density` is the standard-normal density,
and `p1`, `p2` are the Edgeworth polynomials. The structure records the
expansion statement; the concrete cumulant/polynomial calculation remains a
separate proof obligation. -/
structure SecondOrderEdgeworthExpansion
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ → Ω → ℝ) (baseCDF density p1 p2 : ℝ → ℝ) where
  /-- The second-order Edgeworth remainder is `o(n^{-1})` uniformly in `x`. -/
  uniform_scaled_remainder_tendsto_zero :
    TendstoUniformly
      (fun (n : ℕ) x =>
        (n : ℝ) *
          (statisticCDFReal μ T n x - baseCDF x -
            (Real.sqrt (n : ℝ))⁻¹ * (p1 x * density x) -
            (n : ℝ)⁻¹ * (p2 x * density x)))
      (fun _ : ℝ => 0) atTop

omit [Fintype k] [DecidableEq k] in
/-- The even quadratic polynomial shape appearing as `p₁` in Hansen's
Theorem 7.15 Edgeworth expansion.  The concrete coefficients are cumulant
functions of the regression moments; this definition records the textbook
polynomial order and parity. -/
@[reducible]
def edgeworthP1Polynomial (a0 a2 x : ℝ) : ℝ :=
  a0 + a2 * x ^ 2

omit [Fintype k] [DecidableEq k] in
/-- The odd degree-five polynomial shape appearing as `p₂` in Hansen's
Theorem 7.15 Edgeworth expansion. -/
@[reducible]
def edgeworthP2Polynomial (b1 b3 b5 x : ℝ) : ℝ :=
  b1 * x + b3 * x ^ 3 + b5 * x ^ 5

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem edgeworthP1Polynomial_neg (a0 a2 x : ℝ) :
    edgeworthP1Polynomial a0 a2 (-x) = edgeworthP1Polynomial a0 a2 x := by
  simp [edgeworthP1Polynomial]

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem edgeworthP2Polynomial_neg (b1 b3 b5 x : ℝ) :
    edgeworthP2Polynomial b1 b3 b5 (-x) = -edgeworthP2Polynomial b1 b3 b5 x := by
  ring

namespace SecondOrderEdgeworthExpansion

omit [Fintype k] [DecidableEq k] in
/-- A uniform second-order Edgeworth expansion gives the corresponding
pointwise scaled-remainder convergence at every cutoff. -/
theorem pointwise_scaled_remainder_tendsto_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2) (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (statisticCDFReal μ T n x - baseCDF x -
            (Real.sqrt (n : ℝ))⁻¹ * (p1 x * density x) -
            (n : ℝ)⁻¹ * (p2 x * density x)))
      atTop (𝓝 0) := by
  simpa using h.uniform_scaled_remainder_tendsto_zero.tendsto_at x

omit [Fintype k] [DecidableEq k] in
/-- The unscaled second-order Edgeworth approximation error vanishes at each cutoff. -/
theorem pointwise_remainder_tendsto_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2) (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        statisticCDFReal μ T n x - baseCDF x -
          (Real.sqrt (n : ℝ))⁻¹ * (p1 x * density x) -
          (n : ℝ)⁻¹ * (p2 x * density x))
      atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun n =>
    statisticCDFReal μ T n x - baseCDF x -
      (Real.sqrt (n : ℝ))⁻¹ * (p1 x * density x) -
      (n : ℝ)⁻¹ * (p2 x * density x)
  have hscaled : Tendsto (fun n : ℕ => (n : ℝ) * R n) atTop (𝓝 0) := by
    simpa [R] using h.pointwise_scaled_remainder_tendsto_zero x
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ((n : ℝ) * R n))
      atTop (𝓝 0) := by
    simpa using hinv.mul hscaled
  have heq :
      (fun n : ℕ => (n : ℝ)⁻¹ * ((n : ℝ) * R n)) =ᶠ[atTop] R := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hn)
    field_simp [hnne]
  rw [tendsto_congr' heq] at hprod
  simpa [R] using hprod

omit [Fintype k] [DecidableEq k] in
/-- A second-order Edgeworth expansion implies the first-order Edgeworth
interface, with correction `p1(x) * density(x)`. -/
theorem toFirstOrderEdgeworthExpansion
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2) :
    FirstOrderEdgeworthExpansion μ T baseCDF (fun x => p1 x * density x) where
  scaled_cdf_error_tendsto := by
    intro x
    let A : ℝ := p1 x * density x
    let B : ℝ := p2 x * density x
    let R : ℕ → ℝ := fun n =>
      (n : ℝ) *
        (statisticCDFReal μ T n x - baseCDF x -
          (Real.sqrt (n : ℝ))⁻¹ * A -
          (n : ℝ)⁻¹ * B)
    have hR : Tendsto R atTop (𝓝 0) := by
      simpa [R, A, B] using h.pointwise_scaled_remainder_tendsto_zero x
    have hinv_sqrt : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
        atTop (𝓝 (0 : ℝ)) := by
      exact tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hB : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ * B)
        atTop (𝓝 0) :=
      by simpa using hinv_sqrt.mul (tendsto_const_nhds (x := B))
    have hRem : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ * R n)
        atTop (𝓝 0) :=
      by simpa using hinv_sqrt.mul hR
    have hsum : Tendsto
        (fun n : ℕ => A + (Real.sqrt (n : ℝ))⁻¹ * B +
          (Real.sqrt (n : ℝ))⁻¹ * R n)
        atTop (𝓝 A) := by
      simpa using
        ((tendsto_const_nhds (x := A)).add hB).add hRem
    have heq :
        (fun n : ℕ =>
          Real.sqrt (n : ℝ) * (statisticCDFReal μ T n x - baseCDF x)) =ᶠ[atTop]
        (fun n : ℕ => A + (Real.sqrt (n : ℝ))⁻¹ * B +
          (Real.sqrt (n : ℝ))⁻¹ * R n) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr hnpos
      have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
        Real.sq_sqrt hnpos.le
      dsimp [R, A, B]
      rw [← hsqrt_sq]
      field_simp [hsqrt_ne]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      ring
    rw [tendsto_congr' heq]
    simpa [A] using hsum

omit [Fintype k] [DecidableEq k] in
/-- A second-order Edgeworth expansion implies ordinary CDF convergence to the base CDF. -/
theorem cdf_tendsto_base
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2) (x : ℝ) :
    Tendsto (fun n : ℕ => statisticCDFReal μ T n x) atTop (𝓝 (baseCDF x)) :=
  h.toFirstOrderEdgeworthExpansion.cdf_tendsto_base x

omit [Fintype k] [DecidableEq k] in
/-- Symmetric two-sided Edgeworth expansion consequence.

For a symmetric interval, the `n^{-1/2}` correction cancels when `p₁` is even
and the density is even, while the odd `p₂` term contributes twice its positive
cutoff value. This is the formal version of Hansen's explanation after
Theorem 7.15 that two-sided intervals remove the first-order Edgeworth
coverage error. -/
theorem symmetric_interval_scaled_remainder_tendsto_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2) (c : ℝ)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            (baseCDF c - baseCDF (-c)) -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) := by
  have hc := h.pointwise_scaled_remainder_tendsto_zero c
  have hneg := h.pointwise_scaled_remainder_tendsto_zero (-c)
  have hdiff := hc.sub hneg
  have heq :
      (fun n : ℕ =>
        (n : ℝ) *
            (statisticCDFReal μ T n c - baseCDF c -
              (Real.sqrt (n : ℝ))⁻¹ * (p1 c * density c) -
              (n : ℝ)⁻¹ * (p2 c * density c)) -
          (n : ℝ) *
            (statisticCDFReal μ T n (-c) - baseCDF (-c) -
              (Real.sqrt (n : ℝ))⁻¹ * (p1 (-c) * density (-c)) -
              (n : ℝ)⁻¹ * (p2 (-c) * density (-c)))) =ᶠ[atTop]
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            (baseCDF c - baseCDF (-c)) -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c)))) := by
    filter_upwards with n
    rw [hp1, hp2, hdensity]
    ring
  rw [tendsto_congr' heq] at hdiff
  simpa using hdiff

omit [Fintype k] [DecidableEq k] in
/-- Coefficient-specialized version of the symmetric two-sided Edgeworth
cancellation theorem for Hansen's even-quadratic `p₁` and odd degree-five `p₂`
polynomial shapes. -/
theorem symmetric_interval_scaled_remainder_tendsto_zero_polynomial
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            (baseCDF c - baseCDF (-c)) -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  h.symmetric_interval_scaled_remainder_tendsto_zero c
    (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c)
    hdensity

end SecondOrderEdgeworthExpansion

omit [DecidableEq k] in
/-- Numerator of the scalar t-statistic for totalized OLS. -/
@[reducible]
noncomputable def olsLinearTNumeratorStar
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) : ℝ :=
  (root • (R *ᵥ (olsBetaStar X y - β))) ⬝ᵥ (fun _ : Unit => 1)

omit [DecidableEq k] in
/-- Numerator of the scalar t-statistic for the ordinary-on-nonsingular OLS wrapper. -/
@[reducible]
noncomputable def olsLinearTNumeratorOrZero
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) : ℝ :=
  (root • (R *ᵥ (olsBetaOrZero X y - β))) ⬝ᵥ (fun _ : Unit => 1)

omit [DecidableEq k] in
/-- Scalar t-statistic for totalized OLS and an arbitrary covariance estimator. -/
@[reducible]
noncomputable def olsLinearTStatStar
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (Vhat : Matrix k k ℝ)
    (X : Matrix n k ℝ) (y : n → ℝ) (β : k → ℝ) (root : ℝ) : ℝ :=
  olsLinearTNumeratorStar R X y β root /
    linearRestrictionStdError R Vhat

omit [DecidableEq k] in
/-- Scalar t-statistic for ordinary-on-nonsingular OLS and an arbitrary covariance estimator. -/
@[reducible]
noncomputable def olsLinearTStatOrZero
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (Vhat : Matrix k k ℝ)
    (X : Matrix n k ℝ) (y : n → ℝ) (β : k → ℝ) (root : ℝ) : ℝ :=
  olsLinearTNumeratorOrZero R X y β root /
    linearRestrictionStdError R Vhat

omit [DecidableEq k] in
/-- Symmetric confidence-interval membership for a scalar ordinary-OLS restriction. -/
@[reducible]
noncomputable def olsLinearCIEventOrZero
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (Vhat : Matrix k k ℝ)
    (X : Matrix n k ℝ) (y : n → ℝ) (β : k → ℝ) (root crit : ℝ) : Prop :=
  linearRestrictionEstimate R β ∈ Set.Icc
    (linearRestrictionEstimate R (olsBetaOrZero X y) -
      crit * linearRestrictionStdError R Vhat / root)
    (linearRestrictionEstimate R (olsBetaOrZero X y) +
      crit * linearRestrictionStdError R Vhat / root)

omit [DecidableEq k] in
/-- One-degree Wald statistic for a scalar ordinary-OLS restriction. -/
@[reducible]
noncomputable def olsLinearWaldStatOrZero
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (Vhat : Matrix k k ℝ)
    (X : Matrix n k ℝ) (y : n → ℝ) (β : k → ℝ) (root : ℝ) : ℝ :=
  (olsLinearTStatOrZero R Vhat X y β root) ^ 2

@[simp]
theorem olsLinearTNumeratorOrZero_eq_star
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) :
    olsLinearTNumeratorOrZero R X y β root =
      olsLinearTNumeratorStar R X y β root := by
  simp [olsLinearTNumeratorOrZero, olsLinearTNumeratorStar]

@[simp]
theorem olsLinearTStatOrZero_eq_star
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (Vhat : Matrix k k ℝ)
    (X : Matrix n k ℝ) (y : n → ℝ) (β : k → ℝ) (root : ℝ) :
    olsLinearTStatOrZero R Vhat X y β root =
      olsLinearTStatStar R Vhat X y β root := by
  simp [olsLinearTStatOrZero, olsLinearTStatStar]

@[simp]
theorem olsLinearWaldStatOrZero_eq_sq
    {n : Type*} [Fintype n] (R : Matrix Unit k ℝ) (Vhat : Matrix k k ℝ)
    (X : Matrix n k ℝ) (y : n → ℝ) (β : k → ℝ) (root : ℝ) :
    olsLinearWaldStatOrZero R Vhat X y β root =
      (olsLinearTStatOrZero R Vhat X y β root) ^ 2 := rfl

/-- Scaling by positive standard-error and root factors preserves absolute-value inequalities. -/
theorem abs_scaled_error_div_le_iff
    {d root se crit : ℝ}
    (hroot : 0 < root) (hse : 0 < se) :
    |root * d / se| ≤ crit ↔ |d| ≤ crit * se / root := by
  rw [abs_div, abs_mul, abs_of_pos hroot, abs_of_pos hse]
  constructor
  · intro h
    have hmul : root * |d| ≤ crit * se := (div_le_iff₀ hse).mp h
    exact (le_div_iff₀ hroot).mpr (by simpa [mul_comm] using hmul)
  · intro h
    have hmul' : |d| * root ≤ crit * se := (le_div_iff₀ hroot).mp h
    have hmul : root * |d| ≤ crit * se := by
      simpa [mul_comm] using hmul'
    exact (div_le_iff₀ hse).mpr hmul

/-- Symmetric confidence-interval membership is equivalent to an absolute t-statistic bound. -/
theorem mem_symmetric_ci_iff_abs_tstat_le
    {θ θhat root se crit : ℝ}
    (hroot : 0 < root) (hse : 0 < se) :
    θ ∈ Set.Icc (θhat - crit * se / root) (θhat + crit * se / root) ↔
      |root * (θhat - θ) / se| ≤ crit := by
  rw [← Set.mem_Icc_iff_abs_le
    (x := θhat) (y := θ) (z := crit * se / root)]
  exact (abs_scaled_error_div_le_iff
    (d := θhat - θ) (root := root) (se := se) (crit := crit) hroot hse).symm

/-- **Hansen Theorem 7.12, generic symmetric confidence-interval coverage bridge.**

If the absolute t-statistic converges to `|N(0,1)|`, then the probability that
the true scalar parameter lies in the usual symmetric interval converges to the
absolute-standard-normal mass below the critical value, at every continuity
critical value. Positivity of the root and standard error is needed only
eventually, so finite initial sample sizes are ignored by the limit. -/
theorem symmetricCI_coverage_of_abs_tstat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse : ∀ᶠ n in atTop, ∀ ω, 0 < se n ω)
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1))
    (hcrit : ((gaussianReal 0 1).map (fun x : ℝ => |x|))
      (frontier (Set.Iic crit)) = 0) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  have hevent :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
      hT
      (E := Set.Iic crit) measurableSet_Iic hcrit
  refine hevent.congr' ?_
  filter_upwards [hroot, hse] with n hnroot hnse
  congr 1
  ext ω
  have hiff := mem_symmetric_ci_iff_abs_tstat_le
    (θ := θ) (θhat := θhat n ω) (root := root n)
    (se := se n ω) (crit := crit) hnroot (hnse ω)
  simpa [Set.mem_Iic] using hiff.symm

/-- Version of `symmetricCI_coverage_of_abs_tstat` with the standard-normal
continuity-set side condition already discharged. -/
theorem symmetricCI_coverage_of_abs_tstat_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse : ∀ᶠ n in atTop, ∀ ω, 0 < se n ω)
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  symmetricCI_coverage_of_abs_tstat
    (μ := μ) (θ := θ) (crit := crit)
    hroot hse hT (standardNormalAbs_frontier_Iic_null crit)

/-- **Hansen Theorem 7.12, probabilistic symmetric confidence-interval coverage bridge.**

This version removes the pointwise eventual standard-error positivity shortcut:
it is enough that the nonpositive-standard-error event has probability tending
to zero. The interval event and the absolute-t-statistic event can then differ
only on a negligible bad set. -/
theorem symmetricCI_coverage_of_abs_tstat_nonpos_tendsto_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse_nonpos : Tendsto (fun n => μ {ω | se n ω ≤ 0}) atTop (𝓝 0))
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1))
    (hcrit : ((gaussianReal 0 1).map (fun x : ℝ => |x|))
      (frontier (Set.Iic crit)) = 0) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let ci : ℕ → Set Ω := fun n => {ω | θ ∈ Set.Icc
    (θhat n ω - crit * se n ω / root n)
    (θhat n ω + crit * se n ω / root n)}
  let stat : ℕ → Set Ω := fun n =>
    {ω | |root n * (θhat n ω - θ) / se n ω| ∈ Set.Iic crit}
  let bad : ℕ → Set Ω := fun n => {ω | se n ω ≤ 0}
  let L : ℝ≥0∞ := ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit)
  have hstat : Tendsto (fun n => μ (stat n)) atTop (𝓝 L) := by
    have hevent :=
      TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
        hT
        (E := Set.Iic crit) measurableSet_Iic hcrit
    simpa [stat, L] using hevent
  have hsymm_subset : ∀ n, 0 < root n → ci n ∆ stat n ⊆ bad n := by
    intro n hnroot ω hω
    by_cases hnse : 0 < se n ω
    · have hiff := mem_symmetric_ci_iff_abs_tstat_le
        (θ := θ) (θhat := θhat n ω) (root := root n)
        (se := se n ω) (crit := crit) hnroot hnse
      rw [Set.mem_symmDiff] at hω
      rcases hω with hω | hω
      · exact False.elim (hω.2 (hiff.mp hω.1))
      · exact False.elim (hω.2 (hiff.mpr hω.1))
    · exact not_lt.mp hnse
  have hdiff : Tendsto (fun n => μ (ci n ∆ stat n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hse_nonpos
      (Eventually.of_forall fun n => zero_le _) ?_
    filter_upwards [hroot] with n hnroot
    exact measure_mono (hsymm_subset n hnroot)
  have hL_ne_top : L ≠ ∞ := by
    simp [L]
  have hlower : Tendsto (fun n => μ (stat n) - μ (ci n ∆ stat n)) atTop (𝓝 L) := by
    simpa [L] using ENNReal.Tendsto.sub hstat hdiff (Or.inl hL_ne_top)
  have hupper : Tendsto (fun n => μ (stat n) + μ (ci n ∆ stat n)) atTop (𝓝 L) := by
    simpa using hstat.add hdiff
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · exact Eventually.of_forall fun n => by
      have hstat_le : μ (stat n) ≤ μ (ci n) + μ (ci n ∆ stat n) := by
        calc
          μ (stat n) ≤ μ ((ci n ∆ stat n) ∪ ci n) :=
            measure_mono (le_symmDiff_sup_left (ci n) (stat n))
          _ ≤ μ (ci n ∆ stat n) + μ (ci n) := measure_union_le _ _
          _ = μ (ci n) + μ (ci n ∆ stat n) := by rw [add_comm]
      exact tsub_le_iff_right.mpr hstat_le
  · exact Eventually.of_forall fun n => by
      calc
        μ (ci n) ≤ μ ((ci n ∆ stat n) ∪ stat n) :=
          measure_mono (le_symmDiff_sup_right (ci n) (stat n))
        _ ≤ μ (ci n ∆ stat n) + μ (stat n) := measure_union_le _ _
        _ = μ (stat n) + μ (ci n ∆ stat n) := by rw [add_comm]

/-- Standard-normal version of
`symmetricCI_coverage_of_abs_tstat_nonpos_tendsto_zero`. -/
theorem symmetricCI_coverage_of_abs_tstat_standardNormal_nonpos_tendsto_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse_nonpos : Tendsto (fun n => μ {ω | se n ω ≤ 0}) atTop (𝓝 0))
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  symmetricCI_coverage_of_abs_tstat_nonpos_tendsto_zero
    (μ := μ) (θ := θ) (crit := crit)
    hroot hse_nonpos hT (standardNormalAbs_frontier_Iic_null crit)

/-- Standard-normal confidence-interval coverage from convergence in probability
of the standard error to a positive constant. -/
theorem symmetricCI_coverage_of_abs_tstat_standardNormal_se_tendsto_pos
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit c : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hc : 0 < c)
    (hse : TendstoInMeasure μ se atTop (fun _ => c))
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  symmetricCI_coverage_of_abs_tstat_standardNormal_nonpos_tendsto_zero
    (μ := μ) (θ := θ) (crit := crit)
    hroot (tendsto_measure_nonpos_of_tendstoInMeasure_const_pos (μ := μ) hc hse) hT

omit [DecidableEq k] in
/-- Measurability of a scalar standard error induced by any matrix covariance estimator. -/
theorem linearCovarianceStdError_aemeasurable
    {μ : Measure Ω} (R : Matrix Unit k ℝ)
    {Vhat : Ω → Matrix k k ℝ}
    (hVhat : AEStronglyMeasurable Vhat μ) :
    AEMeasurable (fun ω => Real.sqrt ((R * Vhat ω * Rᵀ) () ())) μ := by
  have hcov : AEStronglyMeasurable
      (fun ω => R * Vhat ω * Rᵀ) μ :=
    linMapCov_aestronglyMeasurable
      (μ := μ) (R := R) hVhat
  have hentry_cont : Continuous (fun M : Matrix Unit Unit ℝ => M () ()) :=
    (continuous_apply ()).comp (continuous_apply ())
  have hsqrt_cont : Continuous (fun M : Matrix Unit Unit ℝ => Real.sqrt (M () ())) :=
    Real.continuous_sqrt.comp hentry_cont
  exact (hsqrt_cont.comp_aestronglyMeasurable hcov).aemeasurable

namespace CovarianceEstimatorConsistent

omit [DecidableEq k] in
/-- A consistent covariance estimator gives a consistent scalar standard error
for any fixed one-row linear restriction. -/
theorem toFeasibleLinearStdError
    {μ : Measure Ω} [IsFiniteMeasure μ] {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (h : CovarianceEstimatorConsistent μ Vhat V) (R : Matrix Unit k ℝ)
    (hpos : 0 < linearRestrictionStdError R V) :
    FeasibleStandardErrorConsistent μ
      (fun n ω => Real.sqrt ((R * Vhat n ω * Rᵀ) () ()))
      (linearRestrictionStdError R V) where
  se_measurable := fun n =>
    linearCovarianceStdError_aemeasurable
      (μ := μ) (R := R) (Vhat := fun ω => Vhat n ω)
      (h.covariance_measurable n)
  se_tendsto := by
    simpa [linearRestrictionStdError] using
      linMapCovStdError_tendstoInMeasure
        (μ := μ) (Vhat := Vhat) (V := V) R () h.covariance_measurable
        h.covariance_tendsto
  limit_pos := hpos

end CovarianceEstimatorConsistent

/-- Generic studentization bridge for scalar linear inference.

If a numerator has a distributional limit and the standard error converges in
probability to a positive constant, then the studentized statistic has the
corresponding ratio limit. -/
theorem studentizedLimit_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {num se : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν)
    (hse : TendstoInMeasure μ se atTop (fun _ => c))
    (hse_meas : ∀ n, AEMeasurable (se n) μ) :
    TendstoInDistribution
      (fun n ω => num n ω / se n ω)
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
  have hratio_meas : ∀ n, AEMeasurable (fun ω => num n ω / se n ω) μ :=
    fun n => (hnum.forall_aemeasurable n).div (hse_meas n)
  exact tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    (μ := μ) (ν := ν) (X := num) (Y := se) (Z := Z) (c := c)
    hc hnum hse hse_meas hratio_meas

/-- **Hansen Theorem 7.11, generic nonlinear scalar t-statistic.**

If the scaled scalar plug-in error has a distributional limit and the nonlinear
standard error converges in probability to a positive constant, then the
studentized nonlinear scalar statistic converges to the corresponding ratio
limit. -/
theorem nonlinearScalarTStat_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    {Z : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hnum : TendstoInDistribution
      (fun n ω => root n * (θhat n ω - θ))
      atTop Z (fun _ => μ) ν)
    (hse : TendstoInMeasure μ se atTop (fun _ => c))
    (hse_meas : ∀ n, AEMeasurable (se n) μ) :
    TendstoInDistribution
      (fun n ω => scalarFunctionTStat (θhat n ω) θ (se n ω) (root n))
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
  simpa [scalarFunctionTStat] using
    studentizedLimit_tendstoInDistribution
      (μ := μ) (ν := ν)
      (num := fun n ω => root n * (θhat n ω - θ))
      (se := se) (Z := Z) (c := c)
      hc hnum hse hse_meas

/-- **Hansen Theorem 7.12, nonlinear scalar CI coverage from a signed t limit.**

If a nonlinear scalar t-statistic has the standard-normal limit and its standard
error converges to a positive constant, then the usual symmetric confidence
interval has standard-normal asymptotic coverage. -/
theorem nonlinearScalarCI_coverage_of_tstat_standardNormal_se_tendsto_pos
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit c : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hc : 0 < c)
    (hse : TendstoInMeasure μ se atTop (fun _ => c))
    (hT : TendstoInDistribution
      (fun n ω => scalarFunctionTStat (θhat n ω) θ (se n ω) (root n))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto
      (fun n => μ {ω |
        scalarFunctionCIEvent (θhat n ω) θ (se n ω) (root n) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  have hAbs : TendstoInDistribution
      (fun n ω => |scalarFunctionTStat (θhat n ω) θ (se n ω) (root n)|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    simpa [Function.comp_def] using hT.continuous_comp continuous_abs
  simpa [scalarFunctionCIEvent, scalarFunctionTStat] using
    symmetricCI_coverage_of_abs_tstat_standardNormal_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit) (c := c)
      (θhat := θhat) (se := se) (root := root)
      hroot hc hse hAbs

/-- **Hansen §7.17, homoskedastic t-statistic for a scalar linear function.**

For a one-dimensional fixed linear map `R`, the homoskedastic-studentized
totalized OLS linear function converges to the Gaussian linear-function limit
divided by the homoskedastic population standard-error scale. -/
private theorem olsHomoLinTStatStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatStar R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop
      (fun ω =>
        Z ω / linearRestrictionStdError R (homoAsymCov μ X e))
      (fun _ => μ) ν := by
  let c : ℝ := linearRestrictionStdError R (homoAsymCov μ X e)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHomoCovStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProj_linMap_olsBetaStar_tendstoInDistribution_gaussian_cov
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        hclt.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hmodel hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHomoLinSEStar_tendstoInMeasure
        (μ := μ) (X := X) (e := e) (y := y)
        hvar.toSampleVarianceAssumption74 β R () hmodel hX_meas he_meas
  have hV_meas :=
    olsHomoskedasticCovStar_stack_aestronglyMeasurable_components
      (μ := μ) (X := X) (e := e) (y := y)
      hvar.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    exact linearCovarianceStdError_aemeasurable
      (μ := μ) (R := R)
      (Vhat := fun ω =>
        olsHomoCovStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (hV_meas n)
  have hratio := studentizedLimit_tendstoInDistribution
    (μ := μ) (ν := ν) (num := num) (se := se) (Z := Z) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas
  simpa [num, se, c, olsLinearTStatStar,
    olsLinearTNumeratorStar, linearRestrictionStdError] using hratio

/-- **Hansen Theorem 7.14, scalar homoskedastic t-statistic with standard normal limit.**

If the homoskedastic asymptotic covariance equals the robust sandwich
covariance, the scalar homoskedastic t-statistic has the standard-normal limit.
This is the one-dimensional t-statistic face behind the homoskedastic Wald
statistic. -/
private theorem olsHomoLinTStatStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoAsymCov μ X e =
      heteroAsymCov μ X e)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatStar R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := linearRestrictionStdError R (homoAsymCov μ X e)
  have hentry_pos : 0 < (R * homoAsymCov μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * homoAsymCov μ X e * Rᵀ) () () =
        olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) := by
    rw [hVeq]
    exact linMapCov_unit_apply_eq_olsProjectionAsymVar
      (μ := μ) (X := X) (e := e) hclt.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * homoAsymCov μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHomoLinTStatStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen §7.17 for ordinary OLS on nonsingular samples, homoskedastic face.**

The homoskedastic-studentized scalar linear t-statistic transfers from the
totalized estimator to the ordinary-on-nonsingular wrapper `olsBetaOrZero`. -/
private theorem olsHomoLinTStatOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop
      (fun ω =>
        Z ω / linearRestrictionStdError R (homoAsymCov μ X e))
      (fun _ => μ) ν := by
  simpa using
    olsHomoLinTStatStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      hclt hvar β R hmodel hX_meas he_meas hZ hse_pos

/-- **Hansen Theorem 7.14 for ordinary OLS, homoskedastic standard-normal face.** -/
private theorem olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoAsymCov μ X e =
      heteroAsymCov μ X e)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    olsHomoLinTStatStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos

/-- Absolute-value CMT for the ordinary homoskedastic scalar t-statistic. -/
private theorem olsHomoLinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoAsymCov μ X e =
      heteroAsymCov μ X e)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, homoskedastic confidence-interval coverage.**

For a one-row linear restriction, the ordinary-wrapper homoskedastic symmetric
confidence interval has limiting coverage equal to the absolute standard-normal
mass below the critical value. Sample standard-error positivity is derived from
convergence in probability to the positive population standard error. -/
private theorem olsHomoLinCIOrZero_cov_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoAsymCov μ X e =
      heteroAsymCov μ X e)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHomoCovStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  let c : ℝ := linearRestrictionStdError R (homoAsymCov μ X e)
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHomoLinSEStar_tendstoInMeasure
        (μ := μ) (X := X) (e := e) (y := y)
        hvar.toSampleVarianceAssumption74 β R () hmodel hX_meas he_meas
  have hAbs := olsHomoLinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root, olsLinearTStatOrZero,
        olsLinearTNumeratorOrZero, linearRestrictionStdError]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root, c, olsLinearCIEventOrZero,
    linearRestrictionEstimate, linearRestrictionStdError] using
    symmetricCI_coverage_of_abs_tstat_standardNormal_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root) (c := c)
      hroot (by simpa [c] using hse_pos) hse hGeneric

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, homoskedastic confidence-interval coverage from homoskedasticity.**

This is the variable-facing version: it assumes constant conditional error
variance given regressors, then derives the covariance identity internally. -/
private theorem olsHomoLinCIOrZero_cov_tendsto_standardNormal_homo
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  have hΩ := scoreCovMat_eq_errorVariance_smul_popGram_homo
    (μ := μ) (X := X) (e := e)
    hclt.toSampleCLTAssumption72 hvar.toSampleVarianceAssumption74 hX0 hhomo
  have hQ : IsUnit (popGram μ X).det := by
    simpa [popGram] using hvar.toSampleMomentAssumption71.Q_nonsing
  exact olsHomoLinCIOrZero_cov_tendsto_standardNormal
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R crit hmodel hX_meas he_meas
    (homoAsymCov_eq_heteroAsymCov
      (μ := μ) (X := X) (e := e) hQ hΩ)
    hse_pos

/-- **Hansen Theorem 7.14, scalar one-degree-of-freedom homoskedastic Wald statistic.**

Under the explicit covariance bridge `V⁰β = Vβ`, the scalar homoskedastic Wald
statistic for ordinary OLS converges to `χ²(1)`. -/
private theorem olsHomoLinWaldStatOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoAsymCov μ X e =
      heteroAsymCov μ X e)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, moment-level homoskedastic t-statistic face.**

If the homoskedastic score-covariance identity `Ω = σ²Q` is available, the
ordinary-wrapper scalar homoskedastic t-statistic has a standard-normal limit. -/
private theorem olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal_scoreCov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hΩ : scoreCovMat μ X e = errorVariance μ e • popGram μ X)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  have hQ : IsUnit (popGram μ X).det := by
    simpa [popGram] using hvar.toSampleMomentAssumption71.Q_nonsing
  exact olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas
    (homoAsymCov_eq_heteroAsymCov
      (μ := μ) (X := X) (e := e) hQ hΩ)
    hse_pos

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, homoskedastic t-statistic from homoskedasticity.**

This variable-facing wrapper derives `Ω = σ²Q` from constant conditional error
variance given `X₀`, then applies the covariance-identity bridge. -/
private theorem olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal_homo
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  have hΩ := scoreCovMat_eq_errorVariance_smul_popGram_homo
    (μ := μ) (X := X) (e := e)
    hclt.toSampleCLTAssumption72 hvar.toSampleVarianceAssumption74 hX0 hhomo
  exact olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal_scoreCov
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas hΩ hse_pos

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, moment-level scalar homoskedastic Wald statistic.**

If `Ω = σ²Q`, the scalar one-degree-of-freedom homoskedastic Wald statistic for
ordinary OLS converges to `χ²(1)`. -/
private theorem olsHomoLinWaldStatOrZero_tendstoInDistribution_chiSquared_one_scoreCov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hΩ : scoreCovMat μ X e = errorVariance μ e • popGram μ X)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal_scoreCov
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hΩ hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, scalar homoskedastic Wald statistic from homoskedasticity.** -/
private theorem olsHomoLinWaldStatOrZero_tendstoInDistribution_chiSquared_one_homo
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hse_pos : 0 <
      linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal_homo
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hX0 hhomo hse_pos)

namespace HomoskedasticInferenceConditions

/-- Packaged homoskedastic scalar t-statistic with standard-normal limit. -/
theorem olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : HomoskedasticInferenceConditions μ X e y β)
    (R : Matrix Unit k ℝ)
    (hVeq : homoAsymCov μ X e = heteroAsymCov μ X e)
    (hse_pos : 0 < linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) :=
  HansenEconometrics.olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal
    (μ := μ) (X := X) (e := e) (y := y)
    h.score h.variance β R h.model h.x_aestronglyMeasurable
    h.e_aestronglyMeasurable hVeq hse_pos

/-- Packaged absolute-value CMT for the homoskedastic scalar t-statistic. -/
theorem olsHomoLinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : HomoskedasticInferenceConditions μ X e y β)
    (R : Matrix Unit k ℝ)
    (hVeq : homoAsymCov μ X e = heteroAsymCov μ X e)
    (hse_pos : 0 < linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  HansenEconometrics.olsHomoLinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    h.score h.variance β R h.model h.x_aestronglyMeasurable
    h.e_aestronglyMeasurable hVeq hse_pos

/-- Packaged homoskedastic confidence-interval coverage. -/
theorem olsHomoLinCIOrZero_cov_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : HomoskedasticInferenceConditions μ X e y β)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hVeq : homoAsymCov μ X e = heteroAsymCov μ X e)
    (hse_pos : 0 < linearRestrictionStdError R (homoAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  HansenEconometrics.olsHomoLinCIOrZero_cov_tendsto_standardNormal
    (μ := μ) (X := X) (e := e) (y := y)
    h.score h.variance β R crit h.model h.x_aestronglyMeasurable
    h.e_aestronglyMeasurable hVeq hse_pos

/-- Packaged one-degree homoskedastic Wald statistic. -/
theorem olsHomoLinWaldStatOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : HomoskedasticInferenceConditions μ X e y β)
    (R : Matrix Unit k ℝ)
    (hVeq : homoAsymCov μ X e = heteroAsymCov μ X e)
    (hse_pos : 0 < linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  HansenEconometrics.olsHomoLinWaldStatOrZero_tendstoInDistribution_chiSquared_one
    (μ := μ) (X := X) (e := e) (y := y)
    h.score h.variance β R h.model h.x_aestronglyMeasurable
    h.e_aestronglyMeasurable hVeq hse_pos

end HomoskedasticInferenceConditions

namespace HomoskedasticErrorInferenceConditions

/-- Packaged homoskedastic scalar t-statistic deriving the covariance bridge internally. -/
theorem olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : HomoskedasticErrorInferenceConditions μ X e y β)
    (R : Matrix Unit k ℝ)
    (hse_pos : 0 < linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.x0_measurable)) :=
    h.sigmaFinite_x0
  exact HansenEconometrics.olsHomoLinTStatOrZero_tendstoInDistribution_standardNormal_homo
    (μ := μ) (X := X) (e := e) (y := y)
    h.score h.variance β R h.model h.x_aestronglyMeasurable
    h.e_aestronglyMeasurable h.x0_measurable h.homoskedastic hse_pos

/-- Packaged one-degree homoskedastic Wald statistic deriving the covariance bridge internally. -/
theorem olsHomoLinWaldStatOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : HomoskedasticErrorInferenceConditions μ X e y β)
    (R : Matrix Unit k ℝ)
    (hse_pos : 0 < linearRestrictionStdError R (homoAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.x0_measurable)) :=
    h.sigmaFinite_x0
  exact HansenEconometrics.olsHomoLinWaldStatOrZero_tendstoInDistribution_chiSquared_one_homo
    (μ := μ) (X := X) (e := e) (y := y)
    h.score h.variance β R h.model h.x_aestronglyMeasurable
    h.e_aestronglyMeasurable h.x0_measurable h.homoskedastic hse_pos

end HomoskedasticErrorInferenceConditions

/-- **Hansen Theorem 7.11, HC0 t-statistic for a scalar linear function.**

For a one-dimensional fixed linear map `R`, the HC0-studentized totalized OLS
linear function converges in distribution to the Gaussian linear-function limit
divided by the population standard-error scale. A final law-normalization
corollary can turn this displayed limit into `N(0,1)` once the scalar variance
is identified with the corresponding diagonal of `R Vβ Rᵀ`. -/
theorem olsLinTStatStar_tendstoInDistribution_of_covarianceEstimator
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {covStat : ℕ → Ω → Matrix k k ℝ}
    (hcov : CovarianceEstimatorConsistent μ covStat (heteroAsymCov μ X e))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatStar R
          (covStat n ω)
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop
      (fun ω =>
        Z ω / linearRestrictionStdError R (heteroAsymCov μ X e))
      (fun _ => μ) ν := by
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * covStat n ω * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProj_linMap_olsBetaStar_tendstoInDistribution_gaussian_cov
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hmodel hZ
  have hseCons :=
    hcov.toFeasibleLinearStdError R (by simpa [c] using hse_pos)
  have hratio := studentizedLimit_tendstoInDistribution
    (μ := μ) (ν := ν) (num := num) (se := se) (Z := Z) (c := c)
    hseCons.limit_pos hnum
    (by simpa [se, c] using hseCons.se_tendsto)
    (by simpa [se] using hseCons.se_measurable)
  simpa [num, se, c, olsLinearTStatStar,
    olsLinearTNumeratorStar, linearRestrictionStdError] using hratio

/-- **Hansen Theorem 7.11, HC0 t-statistic for a scalar linear function.**

This constructor wrapper supplies the HC0 covariance-estimator interface from
the current robust covariance proof bundle. -/
private theorem olsHC0LinTStatStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatStar R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop
      (fun ω =>
        Z ω / linearRestrictionStdError R (heteroAsymCov μ X e))
      (fun _ => μ) ν :=
  olsLinTStatStar_tendstoInDistribution_of_covarianceEstimator
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    h β R hmodel
    (covStat := fun n ω =>
      olsHetCovStar (stackRegressors X n ω) (stackOutcomes y n ω))
    { covariance_measurable := fun n =>
        olsHetCovStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          h.toSampleMomentAssumption71 β hmodel hX_meas he_meas n
      covariance_tendsto :=
        olsHetCovStar_tendstoInMeasure_of_bddWts_components
          (μ := μ) (X := X) (e := e) (y := y)
          h.toSampleHC0Assumption76 β hmodel hX_meas he_meas
          hCrossWeight hQuadWeight }
    hZ hse_pos

/-- **Hansen Theorem 7.11, HC0 scalar t-statistic with standard normal limit.**

This is the textbook-facing form of the HC0 studentized scalar linear-function
CLT: the target is the identity random variable under `N(0,1)`. -/
private theorem olsHC0LinTStatStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatStar R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  have hentry_pos : 0 < (R * heteroAsymCov μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * heteroAsymCov μ X e * Rᵀ) () () =
        olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linMapCov_unit_apply_eq_olsProjectionAsymVar
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroAsymCov μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHC0LinTStatStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen Theorem 7.11 for ordinary OLS on nonsingular samples, HC0 face.**

The HC0-studentized scalar linear t-statistic transfers from `olsBetaStar` to
`olsBetaOrZero`, the ordinary-OLS wrapper used on nonsingular sample-Gram
events. -/
private theorem olsHC0LinTStatOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop
      (fun ω =>
        Z ω / linearRestrictionStdError R (heteroAsymCov μ X e))
      (fun _ => μ) ν := by
  simpa using
    olsHC0LinTStatStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos

/-- **Hansen Theorem 7.11 for ordinary OLS, HC0 standard-normal face.** -/
private theorem olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    olsHC0LinTStatStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos

/-- Absolute-value CMT for the ordinary HC0 scalar t-statistic. -/
private theorem olsHC0LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, HC0 confidence-interval coverage.**

The ordinary-wrapper HC0 symmetric confidence interval for a one-row linear
restriction has limiting coverage given by the absolute standard-normal mass
below `crit`; the bad event where the sample HC0 standard error is nonpositive
is negligible because the standard error converges in probability to its
positive population limit. -/
private theorem olsHC0LinCIOrZero_cov_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHetCovStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC0LinSEStar_tendstoInMeasure_of_bddWts_components
        (μ := μ) (X := X) (e := e) (y := y)
        h.toSampleHC0Assumption76 β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hAbs := olsHC0LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root, olsLinearTStatOrZero,
        olsLinearTNumeratorOrZero, linearRestrictionStdError]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root, c, olsLinearCIEventOrZero,
    linearRestrictionEstimate, linearRestrictionStdError] using
    symmetricCI_coverage_of_abs_tstat_standardNormal_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root) (c := c)
      hroot (by simpa [c] using hse_pos) hse hGeneric

/-- Scalar one-degree-of-freedom HC0 Wald statistic for ordinary OLS. -/
private theorem olsHC0LinWaldStatOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

/-- **Hansen Theorem 7.11, HC1 t-statistic for a scalar linear function.**

This is the HC1 analogue of
`olsHC0LinTStatStar_tendstoInDistribution`: the studentized totalized
OLS linear function converges to the same Gaussian limit divided by the
population standard-error scale. -/
private theorem olsHC1LinTStatStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatStar R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop
      (fun ω =>
        Z ω / linearRestrictionStdError R (heteroAsymCov μ X e))
      (fun _ => μ) ν := by
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHetCovHC1Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProj_linMap_olsBetaStar_tendstoInDistribution_gaussian_cov
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hmodel hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC1LinSEStar_tendstoInMeasure_of_bddWts_components
        (μ := μ) (X := X) (e := e) (y := y)
        h.toSampleHC0Assumption76 β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hV_meas :=
    olsHC1CovarianceStar_stack_aestronglyMeasurable_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    exact linearCovarianceStdError_aemeasurable
      (μ := μ) (R := R)
      (Vhat := fun ω =>
        olsHetCovHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (hV_meas n)
  have hratio := studentizedLimit_tendstoInDistribution
    (μ := μ) (ν := ν) (num := num) (se := se) (Z := Z) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas
  simpa [num, se, c, olsLinearTStatStar,
    olsLinearTNumeratorStar, linearRestrictionStdError] using hratio

/-- **Hansen Theorem 7.11, HC1 scalar t-statistic with standard normal limit.**

This is the HC1 analogue of
`olsHC0LinTStatStar_tendstoInDistribution_standardNormal`. -/
private theorem olsHC1LinTStatStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatStar R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  have hentry_pos : 0 < (R * heteroAsymCov μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * heteroAsymCov μ X e * Rᵀ) () () =
        olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linMapCov_unit_apply_eq_olsProjectionAsymVar
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroAsymCov μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHC1LinTStatStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen Theorem 7.11 for ordinary OLS on nonsingular samples, HC1 face.**

The HC1-studentized scalar linear t-statistic transfers from `olsBetaStar` to
the ordinary-on-nonsingular wrapper `olsBetaOrZero`. -/
private theorem olsHC1LinTStatOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop
      (fun ω =>
        Z ω / linearRestrictionStdError R (heteroAsymCov μ X e))
      (fun _ => μ) ν := by
  simpa using
    olsHC1LinTStatStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos

/-- **Hansen Theorem 7.11 for ordinary OLS, HC1 standard-normal face.** -/
private theorem olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    olsHC1LinTStatStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos

/-- Absolute-value CMT for the ordinary HC1 scalar t-statistic. -/
private theorem olsHC1LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

/-- Scalar one-degree-of-freedom HC1 Wald statistic for ordinary OLS. -/
private theorem olsHC1LinWaldStatOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, HC1 confidence-interval coverage.**

The ordinary-wrapper HC1 symmetric confidence interval for a one-row linear
restriction has limiting coverage given by the absolute standard-normal mass
below `crit`; the bad event where the sample HC1 standard error is nonpositive
is negligible because the standard error converges in probability to its
positive population limit. -/
private theorem olsHC1LinCIOrZero_cov_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHetCovHC1Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC1LinSEStar_tendstoInMeasure_of_bddWts_components
        (μ := μ) (X := X) (e := e) (y := y)
        h.toSampleHC0Assumption76 β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hAbs := olsHC1LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root, olsLinearTStatOrZero,
        olsLinearTNumeratorOrZero, linearRestrictionStdError]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root, c, olsLinearCIEventOrZero,
    linearRestrictionEstimate, linearRestrictionStdError] using
    symmetricCI_coverage_of_abs_tstat_standardNormal_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root) (c := c)
      hroot (by simpa [c] using hse_pos) hse hGeneric

/-- Packaged ordinary HC0 scalar t-statistic with standard-normal limit. -/
private theorem hc0_tstat_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) :=
  olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal
    (μ := μ) (X := X) (e := e) (y := y) h β R
    hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hse_pos

set_option linter.style.longLine false in
/-- Packaged absolute-value CMT for the ordinary HC0 scalar t-statistic. -/
private theorem hc0_abs_tstat_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  olsHC0LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y) h β R
    hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hse_pos

/-- Packaged ordinary HC0 confidence-interval coverage. -/
private theorem hc0_ci_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  olsHC0LinCIOrZero_cov_tendsto_standardNormal
    (μ := μ) (X := X) (e := e) (y := y) h β R crit
    hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hse_pos

set_option linter.style.longLine false in
/-- Packaged ordinary HC0 one-degree Wald statistic. -/
private theorem hc0_wald_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  olsHC0LinWaldStatOrZero_tendstoInDistribution_chiSquared_one
    (μ := μ) (X := X) (e := e) (y := y) h β R
    hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hse_pos

/-- Packaged ordinary HC1 scalar t-statistic with standard-normal limit. -/
private theorem hc1_tstat_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) :=
  olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal
    (μ := μ) (X := X) (e := e) (y := y) h β R
    hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hse_pos

set_option linter.style.longLine false in
/-- Packaged absolute-value CMT for the ordinary HC1 scalar t-statistic. -/
private theorem hc1_abs_tstat_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  olsHC1LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y) h β R
    hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hse_pos

/-- Packaged ordinary HC1 confidence-interval coverage. -/
private theorem hc1_ci_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  olsHC1LinCIOrZero_cov_tendsto_standardNormal
    (μ := μ) (X := X) (e := e) (y := y) h β R crit
    hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hse_pos

set_option linter.style.longLine false in
/-- Packaged ordinary HC1 one-degree Wald statistic. -/
private theorem hc1_wald_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  olsHC1LinWaldStatOrZero_tendstoInDistribution_chiSquared_one
    (μ := μ) (X := X) (e := e) (y := y) h β R
    hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hse_pos

set_option linter.style.longLine false in
/-- Packaged ordinary HC2 scalar t-statistic with standard-normal limit. -/
private theorem hc2_tstat_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHetCovHC2Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hentry_pos : 0 < (R * heteroAsymCov μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * heteroAsymCov μ X e * Rᵀ) () () =
        olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linMapCov_unit_apply_eq_olsProjectionAsymVar
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroAsymCov μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hnum : TendstoInDistribution num atTop (fun x : ℝ => c * x)
      (fun _ => μ) (gaussianReal 0 1) := by
    simpa [num] using
      scoreProj_linMap_olsBetaStar_tendstoInDistribution_gaussian_cov
        (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hc.model hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC2LinSEStar_tendstoInMeasure_of_feasibleHCLeverageConditions
        (μ := μ) (X := X) (e := e) (y := y) h β R () hc
  have hV_meas :=
    olsHC2CovarianceStar_stack_aestronglyMeasurable_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hc.model
      hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    exact linearCovarianceStdError_aemeasurable
      (μ := μ) (R := R)
      (Vhat := fun ω =>
        olsHetCovHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (hV_meas n)
  have hratio := studentizedLimit_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (num := num) (se := se)
    (Z := fun x : ℝ => c * x) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas
  have hstat : TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => c * x / c) (fun _ => μ) (gaussianReal 0 1) := by
    simpa [num, se, c, olsLinearTStatOrZero, olsLinearTNumeratorOrZero,
      linearRestrictionStdError] using hratio
  convert hstat using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

set_option linter.style.longLine false in
/-- Packaged absolute-value CMT for the ordinary HC2 scalar t-statistic. -/
private theorem hc2_abs_tstat_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  tendstoInDistribution_abs_real
    (hc2_tstat_feasible_leverage
      (μ := μ) (X := X) (e := e) (y := y) h β R hc hse_pos)

/-- Packaged ordinary HC2 confidence-interval coverage. -/
private theorem hc2_ci_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHetCovHC2Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC2LinSEStar_tendstoInMeasure_of_feasibleHCLeverageConditions
        (μ := μ) (X := X) (e := e) (y := y) h β R () hc
  have hAbs :=
    hc2_abs_tstat_feasible_leverage
      (μ := μ) (X := X) (e := e) (y := y) h β R hc hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root, olsLinearTStatOrZero,
        olsLinearTNumeratorOrZero, linearRestrictionStdError]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root, c, olsLinearCIEventOrZero,
    linearRestrictionEstimate, linearRestrictionStdError] using
    symmetricCI_coverage_of_abs_tstat_standardNormal_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root) (c := c)
      hroot (by simpa [c] using hse_pos) hse hGeneric

set_option linter.style.longLine false in
/-- Packaged ordinary HC2 one-degree Wald statistic. -/
private theorem hc2_wald_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  tendstoInDistribution_sq_standardNormal_chiSquared_one
    (hc2_tstat_feasible_leverage
      (μ := μ) (X := X) (e := e) (y := y) h β R hc hse_pos)

set_option linter.style.longLine false in
/-- Packaged ordinary HC3 scalar t-statistic with standard-normal limit. -/
private theorem hc3_tstat_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHetCovHC3Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hentry_pos : 0 < (R * heteroAsymCov μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * heteroAsymCov μ X e * Rᵀ) () () =
        olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linMapCov_unit_apply_eq_olsProjectionAsymVar
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroAsymCov μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hnum : TendstoInDistribution num atTop (fun x : ℝ => c * x)
      (fun _ => μ) (gaussianReal 0 1) := by
    simpa [num] using
      scoreProj_linMap_olsBetaStar_tendstoInDistribution_gaussian_cov
        (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hc.model hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC3LinSEStar_tendstoInMeasure_of_feasibleHCLeverageConditions
        (μ := μ) (X := X) (e := e) (y := y) h β R () hc
  have hV_meas :=
    olsHC3CovarianceStar_stack_aestronglyMeasurable_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hc.model
      hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    exact linearCovarianceStdError_aemeasurable
      (μ := μ) (R := R)
      (Vhat := fun ω =>
        olsHetCovHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (hV_meas n)
  have hratio := studentizedLimit_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (num := num) (se := se)
    (Z := fun x : ℝ => c * x) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas
  have hstat : TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => c * x / c) (fun _ => μ) (gaussianReal 0 1) := by
    simpa [num, se, c, olsLinearTStatOrZero, olsLinearTNumeratorOrZero,
      linearRestrictionStdError] using hratio
  convert hstat using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

set_option linter.style.longLine false in
/-- Packaged absolute-value CMT for the ordinary HC3 scalar t-statistic. -/
private theorem hc3_abs_tstat_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  tendstoInDistribution_abs_real
    (hc3_tstat_feasible_leverage
      (μ := μ) (X := X) (e := e) (y := y) h β R hc hse_pos)

/-- Packaged ordinary HC3 confidence-interval coverage. -/
private theorem hc3_ci_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHetCovHC3Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  let c : ℝ := linearRestrictionStdError R (heteroAsymCov μ X e)
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC3LinSEStar_tendstoInMeasure_of_feasibleHCLeverageConditions
        (μ := μ) (X := X) (e := e) (y := y) h β R () hc
  have hAbs :=
    hc3_abs_tstat_feasible_leverage
      (μ := μ) (X := X) (e := e) (y := y) h β R hc hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root, olsLinearTStatOrZero,
        olsLinearTNumeratorOrZero, linearRestrictionStdError]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root, c, olsLinearCIEventOrZero,
    linearRestrictionEstimate, linearRestrictionStdError] using
    symmetricCI_coverage_of_abs_tstat_standardNormal_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root) (c := c)
      hroot (by simpa [c] using hse_pos) hse hGeneric

set_option linter.style.longLine false in
/-- Packaged ordinary HC3 one-degree Wald statistic. -/
private theorem hc3_wald_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  tendstoInDistribution_sq_standardNormal_chiSquared_one
    (hc3_tstat_feasible_leverage
      (μ := μ) (X := X) (e := e) (y := y) h β R hc hse_pos)

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC0 scalar t-statistic endpoint. -/
theorem olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) :=
  hc0_tstat_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment absolute-value CMT for the ordinary HC0 scalar t-statistic. -/
theorem olsHC0LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  hc0_abs_tstat_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC0 confidence-interval coverage endpoint. -/
theorem olsHC0LinCIOrZero_cov_tendsto_standardNormal_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ) (crit : ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  hc0_ci_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R crit
    hm.toFeasibleHCRemainderConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC0 one-degree Wald endpoint. -/
theorem olsHC0LinWaldStatOrZero_tendstoInDistribution_chiSquared_one_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  hc0_wald_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC1 scalar t-statistic endpoint. -/
theorem olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) :=
  hc1_tstat_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment absolute-value CMT for the ordinary HC1 scalar t-statistic. -/
theorem olsHC1LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  hc1_abs_tstat_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC1 confidence-interval coverage endpoint. -/
theorem olsHC1LinCIOrZero_cov_tendsto_standardNormal_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ) (crit : ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  hc1_ci_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R crit
    hm.toFeasibleHCRemainderConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC1 one-degree Wald endpoint. -/
theorem olsHC1LinWaldStatOrZero_tendstoInDistribution_chiSquared_one_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  hc1_wald_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC2 scalar t-statistic endpoint. -/
theorem olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) :=
  hc2_tstat_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment absolute-value CMT for the ordinary HC2 scalar t-statistic. -/
theorem olsHC2LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  hc2_abs_tstat_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC2 confidence-interval coverage endpoint. -/
theorem olsHC2LinCIOrZero_cov_tendsto_standardNormal_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ) (crit : ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  hc2_ci_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R crit
    hm.toFeasibleHCLeverageConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC2 one-degree Wald endpoint. -/
theorem olsHC2LinWaldStatOrZero_tendstoInDistribution_chiSquared_one_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  hc2_wald_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC3 scalar t-statistic endpoint. -/
theorem olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) :=
  hc3_tstat_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment absolute-value CMT for the ordinary HC3 scalar t-statistic. -/
theorem olsHC3LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        |olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) :=
  hc3_abs_tstat_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC3 confidence-interval coverage endpoint. -/
theorem olsHC3LinCIOrZero_cov_tendsto_standardNormal_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ) (crit : ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    Tendsto
      (fun n => μ {ω |
        olsLinearCIEventOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)) crit})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  hc3_ci_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R crit
    hm.toFeasibleHCLeverageConditions hse_pos

set_option linter.style.longLine false in
/-- Compact robust-moment ordinary HC3 one-degree Wald endpoint. -/
theorem olsHC3LinWaldStatOrZero_tendstoInDistribution_chiSquared_one_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e)) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        olsLinearWaldStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) :=
  hc3_wald_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hse_pos

/-- **Hansen Theorem 7.3, all scalar projections for totalized OLS with `Ω`.**

For every fixed direction `a`, the scaled totalized OLS error has Gaussian
limit with asymptotic variance `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. This is the complete
projection-family form currently available before the vector/Cramér-Wold
wrapper is formalized. -/
theorem scoreProj_olsBetaStar_tendstoInDistribution_gaussian_cov_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (olsProjectionAsymVar μ X e a).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProj_olsBetaStar_tendstoInDistribution_gaussian_cov
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h.toSampleCLTAssumption72 β a hmodel (hZ a)

/-- **Hansen Theorem 7.3 for ordinary OLS on nonsingular samples, scalar-projection form.**

This transfers the scalar totalized-OLS CLT to `olsBetaOrZero`, which is ordinary
`olsBeta` on the nonsingular sample-Gram event and `0` otherwise. -/
theorem scoreProj_olsBetaOrZero_tendstoInDistribution_gaussian_cov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymVar μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  simpa using
    scoreProj_olsBetaStar_tendstoInDistribution_gaussian_cov
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h.toSampleCLTAssumption72 β a hmodel hZ

/-- **Hansen Theorem 7.3, all scalar projections for ordinary OLS on nonsingular samples.**

This is the textbook-facing projection-family form for `olsBetaOrZero`: for
every fixed direction `a`, ordinary OLS on the nonsingular sample-Gram event has
the same scalar Gaussian limit as the totalized estimator. -/
theorem scoreProj_olsBetaOrZero_tendstoInDistribution_gaussian_cov_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (olsProjectionAsymVar μ X e a).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProj_olsBetaOrZero_tendstoInDistribution_gaussian_cov
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel (hZ a)

/-- **Hansen Theorem 7.3 for literal ordinary OLS under sample-Gram invertibility,
scalar-projection form.**

When every realized stacked sample Gram is invertible, the textbook `olsBeta`
estimator is available pointwise and agrees with `olsBetaOrZero`, so the
ordinary-wrapper scalar projection CLT transfers to the dependent ordinary-OLS
surface. -/
theorem scoreProj_olsBeta_tendstoInDistribution_gaussian_cov_of_invertible
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β a : k → ℝ)
    (hInv : ∀ n ω,
      Invertible ((stackRegressors X n ω)ᵀ * stackRegressors X n ω))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymVar μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          ((letI : Invertible
              ((stackRegressors X n ω)ᵀ * stackRegressors X n ω) := hInv n ω
            olsBeta (stackRegressors X n ω) (stackOutcomes y n ω)) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hOrZero := scoreProj_olsBetaOrZero_tendstoInDistribution_gaussian_cov
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hOrZero
  intro n
  exact ae_of_all μ (fun ω => by
    letI : Invertible ((stackRegressors X n ω)ᵀ * stackRegressors X n ω) :=
      hInv n ω
    change
      (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a =
        (Real.sqrt (n : ℝ) •
          (olsBeta (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a
    rw [olsBetaOrZero_eq_olsBeta])

/-- **Hansen Theorem 7.3, all scalar projections for literal ordinary OLS under
sample-Gram invertibility.** -/
theorem scoreProj_olsBeta_tendstoInDistribution_gaussian_cov_all_of_invertible
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hInv : ∀ n ω,
      Invertible ((stackRegressors X n ω)ᵀ * stackRegressors X n ω))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (olsProjectionAsymVar μ X e a).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            ((letI : Invertible
                ((stackRegressors X n ω)ᵀ * stackRegressors X n ω) := hInv n ω
              olsBeta (stackRegressors X n ω) (stackOutcomes y n ω)) - β)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProj_olsBeta_tendstoInDistribution_gaussian_cov_of_invertible
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hInv hmodel (hZ a)

end Assumption72

end HansenEconometrics
