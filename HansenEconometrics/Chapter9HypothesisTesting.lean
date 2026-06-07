import HansenEconometrics.Chapter7Asymptotics.Inference
import HansenEconometrics.Chapter8Asymptotics

/-!
# Chapter 9 — Hypothesis Testing

This file formalizes the asymptotic theory of hypothesis tests from Hansen's
Chapter 9. The current public surface covers:

* `tTest_rejectionProb_tendsto_of_abs_tstat` — the generic Chapter 9 size
  bridge. If the absolute value of a sequence of test statistics converges in
  distribution to `|N(0, 1)|`, then the rejection probability of the two-sided
  test "reject if `|T| > c`" converges to the absolute-standard-normal mass of
  `(c, ∞)`. This is the asymptotic-size half of Theorem 9.1, stated generically
  so that every Chapter 9 t-test endpoint can reuse it. It is the
  rejection-region counterpart of the Chapter 7 confidence-interval coverage
  bridge `symmetricCI_coverage_of_abs_tstat`.
* `tTest_rejectionProb_tendsto_alpha_of_abs_tstat` and
  `olsHC0LinTTest_rejectionProb_tendsto_alpha` — explicit size-`α` wrappers for
  Theorem 9.1 when the critical value is calibrated to have upper-tail mass
  `α`.
* `chiSquaredTest_rejectionProb_tendsto_of_stat` — the generic Chapter 9
  chi-square rejection bridge. If `Wₙ ⇒ χ²(q)`, then the rejection probability
  of the test "reject if `Wₙ > c`" converges to the `χ²(q)` upper-tail mass.
* `nonlinearOlsWaldTest_rejectionProb_tendsto_alpha_of_chapter7` and
  `nonlinearOlsHomoWaldTest_rejectionProb_tendsto_alpha_of_chapter7` —
  theorem-facing nonlinear Wald wrappers for Theorems 9.2/9.3, composed from
  Chapter 7's nonlinear Delta-method and covariance-consistency wrappers.
* `linMap_olsHC0WaldTest_rejectionProb_tendsto_alpha` and
  `linMap_olsHomoWaldTest_rejectionProb_tendsto_alpha` — Theorems 9.2 and 9.3's
  rejection-probability/size-`α` conclusions for the Chapter 7 robust and
  homoskedastic multivariate Wald statistics.
* `emdLinearJTest_rejectionProb_tendsto_alpha` and
  `clsLinearJTest_rejectionProb_tendsto_alpha` plus
  `emdJTest_rejectionProb_tendsto_alpha_of_chapter8` and
  `clsJTest_rejectionProb_tendsto_alpha_of_chapter8` — the
  minimum-distance testing layer of Theorems 9.4 and 9.5. The nonlinear
  wrappers obtain the estimator-difference limit and chi-square law
  identification from Chapter 8.
* `linMap_olsHomoFStatOrZero_tendstoInDistribution_chiSquaredDivDegrees` and
  `linMap_olsHomoFTest_rejectionProb_tendsto_alpha` — Theorem 9.6's
  linear-hypothesis F-test slice: `F = W⁰ / q`, hence the asymptotic
  `χ²(q) / q` null law.
* `linMap_olsHC0HausmanTest_rejectionProb_tendsto_alpha` and
  `nonlinearHausmanTest_rejectionProb_tendsto_alpha_of_chapter8` — the linear
  and nonlinear Hausman statistic layers of Theorem 9.7.
* `tTest_consistent_of_abs_tstat_tendstoInProbabilityAtTop` and
  `waldTest_consistent_of_stat_tendstoInProbabilityAtTop` — the fixed-alternative
  consistency bridges for Theorems 9.8 and 9.9 once the relevant statistic is
  known to diverge to `+∞` in probability.
* `tTest_localPower_tendsto_of_tstat_shiftedNormal`,
  `tTest_oneSidedLocalPower_tendsto_of_tstat_shiftedNormal`,
  `restrictionWaldStatOrZero_tendstoInDistribution_noncentralChiSquared`, and
  `waldTest_localPower_tendsto_noncentralChiSquared` — local-power bridges for
  Theorems 9.10 and 9.11, including the named noncentral chi-square law induced
  by the shifted Gaussian Wald limit.
* `olsHC0LinTTest_rejectionProb_tendsto` — Theorem 9.1's asymptotic-size half
  for the ordinary-OLS HC0 t-test: the rejection probability of the two-sided
  test converges to `P[|Z| > c]`. The hypotheses are the standard Chapter 7
  robust-inference package, which is stronger than Hansen's bare Assumptions
  7.2/7.3, and the null holds by construction (the t-statistic is centred at
  the true coefficient). See the theorem's own docstring for the precise scope.

The convergence half of Theorem 9.1 — `T(θ₀) →d N(0, 1)` under `H₀` — is
already Hansen Theorem 7.11; see
`olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal` in
`HansenEconometrics/Chapter7Asymptotics/Inference.lean`.

Detailed theorem-by-theorem status lives in `inventory/ch9-inventory.md`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Real Topology ProbabilityTheory ENNReal

namespace HansenEconometrics

open Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {k : Type*} [Fintype k] [DecidableEq k]

@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (Matrix ι κ ℝ) :=
  matrixBorelMeasurableSpace ι κ

attribute [local instance] matrixBorelMeasurableSpaceInst

private lemma matrixBorelSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (Matrix ι κ ℝ) :=
  matrixBorelSpace ι κ

attribute [local instance] matrixBorelSpaceInst

/-- The scaled chi-square law `χ²(q) / q` used for asymptotic F-test limits. -/
noncomputable def chiSquaredDivDegrees (q : ℕ) : Measure ℝ :=
  (chiSquared q).map fun x : ℝ => x / (q : ℝ)

lemma isProbabilityMeasure_chiSquaredDivDegrees {q : ℕ} (hq : 0 < q) :
    IsProbabilityMeasure (chiSquaredDivDegrees q) := by
  haveI : IsProbabilityMeasure (chiSquared q) := isProbabilityMeasure_chiSquared hq
  change IsProbabilityMeasure ((chiSquared q).map fun x : ℝ => x / (q : ℝ))
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance instIsProbabilityMeasureChiSquaredDivDegrees {q : ℕ} [Fact (0 < q)] :
    IsProbabilityMeasure (chiSquaredDivDegrees q) :=
  isProbabilityMeasure_chiSquaredDivDegrees (q := q) Fact.out

/-- Noncentral chi-square law induced by a shifted Gaussian Wald quadratic form.

For Hansen's local Wald theorem this is the law of
`Z' V⁻¹ Z` when `Z ∼ N(mean, V)`. Its noncentrality parameter is
`mean' V⁻¹ mean`, exposed separately by `noncentralityParam`. -/
noncomputable def noncentralChiSquared
    (q : ℕ) (mean : Fin q → ℝ) (V : Matrix (Fin q) (Fin q) ℝ) : Measure ℝ :=
  (multivariateGaussian (WithLp.toLp 2 mean) V).map
    fun z : EuclideanSpace ℝ (Fin q) =>
      (z : Fin q → ℝ) ⬝ᵥ (V⁻¹ *ᵥ (z : Fin q → ℝ))

instance instIsProbabilityMeasureNoncentralChiSquared
    {q : ℕ} {mean : Fin q → ℝ} {V : Matrix (Fin q) (Fin q) ℝ} :
    IsProbabilityMeasure (noncentralChiSquared q mean V) := by
  change IsProbabilityMeasure
    ((multivariateGaussian (WithLp.toLp 2 mean) V).map
      fun z : EuclideanSpace ℝ (Fin q) =>
        (z : Fin q → ℝ) ⬝ᵥ (V⁻¹ *ᵥ (z : Fin q → ℝ)))
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Hansen's noncentrality parameter `λ = h' V⁻¹ h`. -/
noncomputable def noncentralityParam
    {q : ℕ} (h : Fin q → ℝ) (V : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  h ⬝ᵥ (V⁻¹ *ᵥ h)

/-- A shifted Gaussian Wald quadratic form has the named noncentral chi-square law. -/
theorem hasLaw_gaussian_mahalanobis_noncentralChiSquared
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    {q : ℕ} {mean : Fin q → ℝ} {V : Matrix (Fin q) (Fin q) ℝ}
    {Z : Ω' → EuclideanSpace ℝ (Fin q)}
    (hZ : HasLaw Z (multivariateGaussian (WithLp.toLp 2 mean) V) ν) :
    HasLaw
      (fun ω => (Z ω : Fin q → ℝ) ⬝ᵥ (V⁻¹ *ᵥ (Z ω : Fin q → ℝ)))
      (noncentralChiSquared q mean V) ν := by
  let f : EuclideanSpace ℝ (Fin q) → ℝ := fun z =>
    (z : Fin q → ℝ) ⬝ᵥ (V⁻¹ *ᵥ (z : Fin q → ℝ))
  have hcoord : Continuous (fun z : EuclideanSpace ℝ (Fin q) => (z : Fin q → ℝ)) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin q => ℝ)
  have hdot : Continuous (fun p : (Fin q → ℝ) × (Fin q → ℝ) => p.1 ⬝ᵥ p.2) :=
    Continuous.dotProduct continuous_fst continuous_snd
  have hmulVec : Continuous (fun z : EuclideanSpace ℝ (Fin q) =>
      V⁻¹ *ᵥ (z : Fin q → ℝ)) :=
    Continuous.matrix_mulVec continuous_const hcoord
  have hf : Continuous f :=
    hdot.comp (hcoord.prodMk hmulVec)
  refine ⟨hf.measurable.comp_aemeasurable hZ.aemeasurable, ?_⟩
  calc
    ν.map (fun ω => f (Z ω)) = (ν.map Z).map f := by
      exact (AEMeasurable.map_map_of_aemeasurable
        hf.aemeasurable hZ.aemeasurable).symm
    _ = (multivariateGaussian (WithLp.toLp 2 mean) V).map f := by
      rw [hZ.map_eq]

/-- Multivariate linear-hypothesis Wald statistic for totalized ordinary OLS.

This is the Chapter 9 textbook-facing statistic for a linear map `R`, written
with `olsBetaOrZero` and an arbitrary covariance estimator `Vhat`. It is the
multivariate analogue of the one-row `olsLinearWaldStatOrZero`. -/
noncomputable def linMapOlsWaldStatOrZero
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) : ℝ :=
  let d : Fin r → ℝ := R *ᵥ (root • (olsBetaOrZero X y - β))
  d ⬝ᵥ (((R * Vhat * Rᵀ)⁻¹) *ᵥ d)

/-- Linear-hypothesis F statistic, written as the homoskedastic Wald statistic divided by `q`.

The covariance estimator argument is kept explicit so the definition can share
the same notation as `linMapOlsWaldStatOrZero`; Theorem 9.6 uses the
homoskedastic covariance estimator. -/
noncomputable def linMapOlsFStatOrZero
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) : ℝ :=
  linMapOlsWaldStatOrZero R Vhat X y β root / (r : ℝ)

/-- Hansen's linear-hypothesis identity `F = W⁰ / q` in statistic form. -/
@[simp]
theorem linMapOlsFStatOrZero_eq_wald_div
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) :
    linMapOlsFStatOrZero R Vhat X y β root =
      linMapOlsWaldStatOrZero R Vhat X y β root / (r : ℝ) :=
  rfl

/-- Linear-hypothesis Hausman statistic in its quadratic-difference form.

For linear restrictions, the restricted estimator drops out after applying
`R`; under the null this statistic is algebraically the Wald statistic. -/
noncomputable def linMapOlsHausmanStatOrZero
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) : ℝ :=
  let d : k → ℝ := root • (olsBetaOrZero X y - β)
  d ⬝ᵥ ((Rᵀ * (R * Vhat * Rᵀ)⁻¹ * R) *ᵥ d)

/-- Hansen's linear-hypothesis Hausman/Wald identity. -/
@[simp]
theorem linMapOlsHausmanStatOrZero_eq_wald
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) :
    linMapOlsHausmanStatOrZero R Vhat X y β root =
      linMapOlsWaldStatOrZero R Vhat X y β root := by
  let d : k → ℝ := root • (olsBetaOrZero X y - β)
  let A : Matrix (Fin r) (Fin r) ℝ := (R * Vhat * Rᵀ)⁻¹
  change d ⬝ᵥ ((Rᵀ * A * R) *ᵥ d) =
    (R *ᵥ d) ⬝ᵥ (A *ᵥ (R *ᵥ d))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact (mulVec_dotProduct_right R d (A *ᵥ (R *ᵥ d))).symm

/-- Efficient minimum-distance criterion statistic for linear hypotheses.

For linear restrictions Hansen shows `J* = W`; this definition exposes the
minimum-distance name while keeping `linMapOlsWaldStatOrZero` as the canonical
linear-hypothesis quadratic-form implementation. -/
noncomputable def emdLinearJStatOrZero
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) : ℝ :=
  linMapOlsWaldStatOrZero R Vhat X y β root

/-- Homoskedastic constrained-least-squares minimum-distance statistic for linear hypotheses.

For linear restrictions Hansen shows the homoskedastic minimum-distance
criterion statistic equals the homoskedastic Wald statistic. -/
noncomputable def clsLinearJStatOrZero
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) : ℝ :=
  linMapOlsWaldStatOrZero R Vhat X y β root

/-- Hansen's linear-hypothesis identity `J* = W` for efficient minimum-distance tests. -/
@[simp]
theorem emdLinearJStatOrZero_eq_wald
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) :
    emdLinearJStatOrZero R Vhat X y β root =
      linMapOlsWaldStatOrZero R Vhat X y β root :=
  rfl

/-- Hansen's linear-hypothesis identity between homoskedastic MD and homoskedastic Wald tests. -/
@[simp]
theorem clsLinearJStatOrZero_eq_wald
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) :
    clsLinearJStatOrZero R Vhat X y β root =
      linMapOlsWaldStatOrZero R Vhat X y β root :=
  rfl

/-! ### Nonlinear Chapter 9 statistic layer -/

/-- Canonical Wald quadratic form for a possibly nonlinear restriction vector.

The input `gap` is the scaled restriction gap, e.g.
`√n • (r(βhat) - θ₀)`, and `VthetaHat` is the plug-in covariance estimator for
that restriction. -/
noncomputable def restrictionWaldStatOrZero
    {r : ℕ} (gap : Fin r → ℝ) (VthetaHat : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  gap ⬝ᵥ (VthetaHat⁻¹ *ᵥ gap)

/-- Hansen's nonlinear OLS Wald statistic.

Here `rfun` is Hansen's nonlinear restriction map `r(β)`, `θ0` is the null
value, `Rhat` is the derivative matrix `∂r(βhat)' / ∂β`, and `Vhat` is the
coefficient covariance estimator. -/
noncomputable def nonlinearOlsWaldStatOrZero
    {r : ℕ} {n : Type*} [Fintype n]
    (rfun : (k → ℝ) → (Fin r → ℝ)) (θ0 : Fin r → ℝ)
    (Rhat : Matrix k (Fin r) ℝ) (Vhat : Matrix k k ℝ)
    (X : Matrix n k ℝ) (y : n → ℝ) (root : ℝ) : ℝ :=
  restrictionWaldStatOrZero
    (root • (rfun (olsBetaOrZero X y) - θ0))
    (Rhatᵀ * Vhat * Rhat)

/-- Criterion quadratic form used by nonlinear EMD/CLS tests.

The input `diff` is the scaled estimator difference, typically
`√n • (βhat - βtilde)`, and `Vhat` is the coefficient covariance/weight matrix
appearing in Hansen's criterion statistic. -/
noncomputable def criterionJStatOrZero
    (diff : k → ℝ) (Vhat : Matrix k k ℝ) : ℝ :=
  diff ⬝ᵥ (Vhat⁻¹ *ᵥ diff)

/-- Hansen's efficient minimum-distance criterion statistic
`n(βhat - βtilde)' Vhat⁻¹ (βhat - βtilde)`. -/
noncomputable def emdJStatOrZero
    (Vhat : Matrix k k ℝ) (bhat btilde : k → ℝ) (root : ℝ) : ℝ :=
  criterionJStatOrZero (root • (bhat - btilde)) Vhat

/-- Hansen's homoskedastic constrained-least-squares criterion statistic, at
the same abstraction layer as `emdJStatOrZero`. -/
noncomputable def clsJStatOrZero
    (Vhat : Matrix k k ℝ) (bhat btilde : k → ℝ) (root : ℝ) : ℝ :=
  criterionJStatOrZero (root • (bhat - btilde)) Vhat

/-- Hansen's nonlinear Hausman statistic.

This is the reduced-rank quadratic form
`n(βhat - βtilde)' Rhat (Rhat' Vhat Rhat)⁻¹ Rhat' (βhat - βtilde)`.
The total inverse is used, matching the repo's Star/OrZero convention. -/
noncomputable def nonlinearHausmanStatOrZero
    {r : ℕ} (Rhat : Matrix k (Fin r) ℝ) (Vhat : Matrix k k ℝ)
    (bhat btilde : k → ℝ) (root : ℝ) : ℝ :=
  let d : k → ℝ := root • (bhat - btilde)
  d ⬝ᵥ ((Rhat * (Rhatᵀ * Vhat * Rhat)⁻¹ * Rhatᵀ) *ᵥ d)

omit [Fintype k] [DecidableEq k] in
/-- Slutsky bridge for a quadratic form with an estimated matrix.

If `Tₙ ⇒ Z` and `Ahatₙ →ₚ A`, then
`Tₙ' Ahatₙ Tₙ ⇒ Z' A Z`. This is the statistic-level CMT used by the
nonlinear Hausman layer. -/
private theorem quadraticForm_tendstoInDistribution_of_vector_and_matrix
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Ahat : ℕ → Ω → Matrix q q ℝ} {A : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A)) :
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ (Ahat n ω *ᵥ T n ω))
      atTop (fun ω => Z ω ⬝ᵥ (A *ᵥ Z ω)) (fun _ => μ) ν := by
  letI : BorelSpace (Matrix q q ℝ) := ⟨rfl⟩
  have hA_meas' : ∀ n, AEMeasurable (Ahat n) μ :=
    fun n => (hA_meas n).aemeasurable
  have hdot : Continuous (fun p : (q → ℝ) × (q → ℝ) => p.1 ⬝ᵥ p.2) :=
    Continuous.dotProduct continuous_fst continuous_snd
  have hmulVec : Continuous
      (fun p : (q → ℝ) × Matrix q q ℝ => p.2 *ᵥ p.1) :=
    Continuous.matrix_mulVec continuous_snd continuous_fst
  have hquad : Continuous
      (fun p : (q → ℝ) × Matrix q q ℝ => p.1 ⬝ᵥ (p.2 *ᵥ p.1)) :=
    hdot.comp (continuous_fst.prodMk hmulVec)
  have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (q → ℝ) × Matrix q q ℝ => p.1 ⬝ᵥ (p.2 *ᵥ p.1))
    hquad hA hA_meas'
  simpa [Function.comp_def] using hraw

omit [Fintype k] [DecidableEq k] in
/-- Wald statistic-level theorem for nonlinear restrictions.

This is Hansen Theorems 9.2/9.3 at the reusable statistic layer: once the
scaled nonlinear restriction gap is asymptotically Gaussian and the plug-in
restriction covariance is consistent, the nonlinear Wald statistic has a
`χ²(r)` null limit. -/
theorem restrictionWaldStatOrZero_tendstoInDistribution_chiSquared
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {r : ℕ} [Fact (0 < r)]
    {T : ℕ → Ω → Fin r → ℝ}
    {Z : Ω' → EuclideanSpace ℝ (Fin r)}
    {VthetaHat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    {Vtheta : Matrix (Fin r) (Fin r) ℝ}
    (hT : TendstoInDistribution T atTop
      (fun ω i => (Z ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hZ : HasLaw Z (multivariateGaussian 0 Vtheta) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (VthetaHat n) μ)
    (hV : TendstoInMeasure μ VthetaHat atTop (fun _ => Vtheta))
    (hV_posDef : Vtheta.PosDef) :
    TendstoInDistribution
      (fun n ω => restrictionWaldStatOrZero (T n ω) (VthetaHat n ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa [restrictionWaldStatOrZero] using
    waldQuadForm_tendstoInDistribution_chiSquared_gaussian_mahalanobis
      (μ := μ) (ν := ν) (r := r)
      (T := T) (Z := Z) (Vhat := VthetaHat) (V := Vtheta)
      hT hZ hV_meas hV hV_posDef

/-- Hansen nonlinear OLS Wald statistic, expressed with the plug-in derivative
and coefficient covariance estimator. -/
theorem nonlinearOlsWaldStatOrZero_tendstoInDistribution_chiSquared
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {r : ℕ} [Fact (0 < r)]
    {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (rfun : (k → ℝ) → (Fin r → ℝ)) (θ0 : Fin r → ℝ)
    {root : ℕ → ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {Z : Ω' → EuclideanSpace ℝ (Fin r)}
    {Vtheta : Matrix (Fin r) (Fin r) ℝ}
    (hT : TendstoInDistribution
      (fun n ω =>
        root n •
          (rfun (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)) - θ0))
      atTop (fun ω i => (Z ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hZ : HasLaw Z (multivariateGaussian 0 Vtheta) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (Rhat n ω)ᵀ * Vhat n ω * Rhat n ω) μ)
    (hV : TendstoInMeasure μ
      (fun n ω => (Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)
      atTop (fun _ => Vtheta))
    (hV_posDef : Vtheta.PosDef) :
    TendstoInDistribution
      (fun n ω =>
        nonlinearOlsWaldStatOrZero rfun θ0 (Rhat n ω) (Vhat n ω)
          (stackRegressors X n ω) (stackOutcomes y n ω) (root n))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa [nonlinearOlsWaldStatOrZero] using
    restrictionWaldStatOrZero_tendstoInDistribution_chiSquared
      (μ := μ) (ν := ν) (r := r)
      (T := fun n ω =>
        root n •
          (rfun (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)) - θ0))
      (Z := Z)
      (VthetaHat := fun n ω => (Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)
      (Vtheta := Vtheta)
      hT hZ hV_meas hV hV_posDef

omit [Fintype k] [DecidableEq k] in
/-- Local-alternative Wald statistic theorem with a named noncentral chi-square limit.

If the scaled restriction gap converges to `N(mean, Vtheta)` and the plug-in
restriction covariance consistently estimates `Vtheta`, then Hansen's Wald
quadratic form converges to the noncentral chi-square law with noncentrality
`mean' Vtheta⁻¹ mean`. -/
theorem restrictionWaldStatOrZero_tendstoInDistribution_noncentralChiSquared
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {r : ℕ}
    {T : ℕ → Ω → Fin r → ℝ}
    {Z : Ω' → EuclideanSpace ℝ (Fin r)}
    {VthetaHat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    {Vtheta : Matrix (Fin r) (Fin r) ℝ}
    {mean : Fin r → ℝ}
    (hT : TendstoInDistribution T atTop
      (fun ω i => (Z ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hZ : HasLaw Z (multivariateGaussian (WithLp.toLp 2 mean) Vtheta) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (VthetaHat n) μ)
    (hV : TendstoInMeasure μ VthetaHat atTop (fun _ => Vtheta))
    (hV_nonsing : IsUnit Vtheta.det) :
    TendstoInDistribution
      (fun n ω => restrictionWaldStatOrZero (T n ω) (VthetaHat n ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (noncentralChiSquared r mean Vtheta) := by
  have hquad := waldQuadForm_tendstoInDistribution_of_vector_and_covariance
    (μ := μ) (ν := ν) (q := Fin r)
    (T := T) (Z := fun ω i => (Z ω : Fin r → ℝ) i)
    (Vhat := VthetaHat) (V := Vtheta)
    hT hV_meas hV hV_nonsing
  have hLaw :
      HasLaw
        (fun ω => (fun i : Fin r => (Z ω : Fin r → ℝ) i) ⬝ᵥ
          (Vtheta⁻¹ *ᵥ (fun i : Fin r => (Z ω : Fin r → ℝ) i)))
        (noncentralChiSquared r mean Vtheta) ν := by
    simpa using
      hasLaw_gaussian_mahalanobis_noncentralChiSquared
        (ν := ν) (q := r) (mean := mean) (V := Vtheta) (Z := Z) hZ
  exact tendstoInDistribution_id_of_hasLaw_limit_real
    (by simpa [restrictionWaldStatOrZero] using hquad) hLaw

/-- Criterion-statistic chi-square theorem from a quadratic-form limit law.

This is the reusable form behind nonlinear EMD/CLS tests: the theorem proves
the convergence of the feasible criterion statistic itself. The final
`χ²(df)` identification is supplied as a law of the limiting quadratic form,
which allows singular rank-`df` Gaussian limits such as the MD difference. -/
theorem criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → Ω → k → ℝ} {Z : Ω' → k → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun n ω => criterionJStatOrZero (T n ω) (Vhat n ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  have hquad :=
    waldQuadForm_tendstoInDistribution_of_vector_and_covariance
      (μ := μ) (ν := ν) (q := k)
      (T := T) (Z := Z) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_nonsing
  exact tendstoInDistribution_id_of_hasLaw_limit_real
    (by simpa [criterionJStatOrZero] using hquad) hLaw

/-- Efficient-MD criterion statistic convergence, with the MD-difference limit
law supplied by the caller. -/
theorem emdJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {df : ℕ} [Fact (0 < df)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    {Z : Ω' → k → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (hDiff : TendstoInDistribution (fun n ω => root n • (bhat n ω - btilde n ω))
      atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun n ω => emdJStatOrZero (Vhat n ω) (bhat n ω) (btilde n ω) (root n))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  simpa [emdJStatOrZero] using
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := μ) (ν := ν) (df := df)
      (T := fun n ω => root n • (bhat n ω - btilde n ω))
      (Z := Z) (Vhat := Vhat) (V := V)
      hDiff hV_meas hV hV_nonsing hLaw

/-- Homoskedastic CLS criterion statistic convergence, with the CLS-difference
limit law supplied by the caller. -/
theorem clsJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {df : ℕ} [Fact (0 < df)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    {Z : Ω' → k → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (hDiff : TendstoInDistribution (fun n ω => root n • (bhat n ω - btilde n ω))
      atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun n ω => clsJStatOrZero (Vhat n ω) (bhat n ω) (btilde n ω) (root n))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  simpa [clsJStatOrZero] using
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := μ) (ν := ν) (df := df)
      (T := fun n ω => root n • (bhat n ω - btilde n ω))
      (Z := Z) (Vhat := Vhat) (V := V)
      hDiff hV_meas hV hV_nonsing hLaw

omit [DecidableEq k] in
/-- Nonlinear Hausman statistic convergence from the Gaussian limit of the
estimator difference and the probability limit of the Hausman quadratic matrix. -/
theorem nonlinearHausmanStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {df : ℕ} [Fact (0 < df)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    {Z : Ω' → k → ℝ}
    {Ahat : ℕ → Ω → Matrix k k ℝ} {A : Matrix k k ℝ}
    (hDiff : TendstoInDistribution (fun n ω => root n • (bhat n ω - btilde n ω))
      atTop Z (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A))
    (hLaw : HasLaw (fun ω => Z ω ⬝ᵥ (A *ᵥ Z ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun n ω => (root n • (bhat n ω - btilde n ω)) ⬝ᵥ
        (Ahat n ω *ᵥ (root n • (bhat n ω - btilde n ω))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  have hquad := quadraticForm_tendstoInDistribution_of_vector_and_matrix
    (μ := μ) (ν := ν) (q := k)
    (T := fun n ω => root n • (bhat n ω - btilde n ω))
    (Z := Z) (Ahat := Ahat) (A := A)
    hDiff hA_meas hA
  exact tendstoInDistribution_id_of_hasLaw_limit_real hquad hLaw

omit [DecidableEq k] in
/-- Nonlinear Hausman statistic convergence, stated with Hansen's derivative/covariance
plug-in matrix rather than an already-assembled quadratic matrix. -/
theorem nonlinearHausmanStatOrZero_tendstoInDistribution_chiSquared_of_matrixLimit
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {r df : ℕ} [Fact (0 < df)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {Z : Ω' → k → ℝ}
    {A : Matrix k k ℝ}
    (hDiff : TendstoInDistribution (fun n ω => root n • (bhat n ω - btilde n ω))
      atTop Z (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable
      (fun ω => Rhat n ω * ((Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)⁻¹ * (Rhat n ω)ᵀ) μ)
    (hA : TendstoInMeasure μ
      (fun n ω => Rhat n ω * ((Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)⁻¹ * (Rhat n ω)ᵀ)
      atTop (fun _ => A))
    (hLaw : HasLaw (fun ω => Z ω ⬝ᵥ (A *ᵥ Z ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun n ω =>
        nonlinearHausmanStatOrZero (Rhat n ω) (Vhat n ω)
          (bhat n ω) (btilde n ω) (root n))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  simpa [nonlinearHausmanStatOrZero] using
    nonlinearHausmanStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := μ) (ν := ν) (df := df)
      (bhat := bhat) (btilde := btilde) (root := root)
      (Z := Z)
      (Ahat := fun n ω =>
        Rhat n ω * ((Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)⁻¹ * (Rhat n ω)ᵀ)
      (A := A) hDiff hA_meas hA hLaw

/-- The absolute standard-normal law has no atom at the frontier of `(c, ∞)`.

The frontier of `Set.Ioi c` is the singleton `{c}`, exactly the frontier of
`Set.Iic c`, so this reduces to `standardNormalAbs_frontier_Iic_null`. -/
private theorem standardNormalAbs_frontier_Ioi_null (crit : ℝ) :
    ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (frontier (Set.Ioi crit)) = 0 := by
  have hfr : frontier (Set.Ioi crit) = frontier (Set.Iic crit) := by
    rw [frontier_Ioi, frontier_Iic]
  rw [hfr]
  exact standardNormalAbs_frontier_Iic_null crit

/-- The absolute value of a shifted `N(mean, 1)` law has no atom at the
frontier of `(-∞, c]`. -/
private theorem normalAbs_frontier_Iic_null (mean crit : ℝ) :
    ((gaussianReal mean 1).map (fun x : ℝ => |x|)) (frontier (Set.Iic crit)) = 0 := by
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
  haveI : NoAtoms (gaussianReal mean 1) :=
    noAtoms_gaussianReal (μ := mean) (v := 1) (by norm_num)
  exact measure_mono_null hpre_subset
    (measure_union_null (measure_singleton crit) (measure_singleton (-crit)))

/-- The absolute value of a shifted `N(mean, 1)` law has no atom at the
frontier of `(c, ∞)`. -/
private theorem normalAbs_frontier_Ioi_null (mean crit : ℝ) :
    ((gaussianReal mean 1).map (fun x : ℝ => |x|)) (frontier (Set.Ioi crit)) = 0 := by
  have hfr : frontier (Set.Ioi crit) = frontier (Set.Iic crit) := by
    rw [frontier_Ioi, frontier_Iic]
  rw [hfr]
  exact normalAbs_frontier_Iic_null mean crit

/-- A shifted `N(mean, 1)` law has no atom at the frontier of `(c, ∞)`. -/
private theorem normal_frontier_Ioi_null (mean crit : ℝ) :
    (gaussianReal mean 1) (frontier (Set.Ioi crit)) = 0 := by
  haveI : NoAtoms (gaussianReal mean 1) :=
    noAtoms_gaussianReal (μ := mean) (v := 1) (by norm_num)
  rw [frontier_Ioi]
  exact measure_singleton crit

/-- Reusable asymptotic-size bridge for two-sided t tests.

If the absolute value of a sequence of test statistics `T` converges in
distribution to `|N(0, 1)|`, then the probability of the rejection region
`{|T| > c}` converges to the absolute-standard-normal mass of `(c, ∞)`.

This is the rejection-region counterpart of the Chapter 7 confidence-interval
coverage bridge `symmetricCI_coverage_of_abs_tstat`. -/
theorem tTest_rejectionProb_tendsto_of_abs_tstat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {crit : ℝ}
    (hT : TendstoInDistribution (fun n ω => |T n ω|) atTop
      (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto (fun n => μ {ω | crit < |T n ω|}) atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Ioi crit))) := by
  have h := TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
    hT (E := Set.Ioi crit) measurableSet_Ioi
    (standardNormalAbs_frontier_Ioi_null crit)
  simpa only [Set.mem_Ioi] using h

/-- Size-`α` wrapper for `tTest_rejectionProb_tendsto_of_abs_tstat`.

If the two-sided critical value is calibrated so that the absolute-standard-normal
upper-tail mass is `α`, then the rejection probability converges to `α`. -/
theorem tTest_rejectionProb_tendsto_alpha_of_abs_tstat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Ioi crit) = alpha)
    (hT : TendstoInDistribution (fun n ω => |T n ω|) atTop
      (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto (fun n => μ {ω | crit < |T n ω|}) atTop (𝓝 alpha) := by
  simpa [hcrit] using
    tTest_rejectionProb_tendsto_of_abs_tstat (μ := μ) (T := T) (crit := crit) hT

/-- Reusable shifted-normal local-power bridge for two-sided t tests.

If the absolute t statistic converges in distribution to `|N(δ, 1)|` under a
local alternative, then the rejection probability of the rule `{|Tₙ| > c}`
converges to the shifted-normal two-sided tail probability. -/
theorem tTest_localPower_tendsto_of_abs_tstat_shiftedNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {crit delta : ℝ}
    (hT : TendstoInDistribution (fun n ω => |T n ω|) atTop
      (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal delta 1)) :
    Tendsto (fun n => μ {ω | crit < |T n ω|}) atTop
      (𝓝 (((gaussianReal delta 1).map (fun x : ℝ => |x|)) (Set.Ioi crit))) := by
  have h := TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
    hT (E := Set.Ioi crit) measurableSet_Ioi
    (normalAbs_frontier_Ioi_null delta crit)
  simpa only [Set.mem_Ioi] using h

/-- Reusable local-power bridge from a shifted-normal t limit.

If the t statistic converges to `N(δ, 1)` under a local alternative, then the
two-sided rejection probability converges to `P(|N(δ,1)| > c)`. In Hansen's
notation, the shift `δ` is the local-alternative drift determined by `h` and
the asymptotic variance. -/
theorem tTest_localPower_tendsto_of_tstat_shiftedNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {crit delta : ℝ}
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x)
      (fun _ => μ) (gaussianReal delta 1)) :
    Tendsto (fun n => μ {ω | crit < |T n ω|}) atTop
      (𝓝 (((gaussianReal delta 1).map (fun x : ℝ => |x|)) (Set.Ioi crit))) := by
  have hAbs : TendstoInDistribution (fun n ω => |T n ω|) atTop
      (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal delta 1) := by
    simpa [Function.comp_def] using hT.continuous_comp continuous_abs
  exact tTest_localPower_tendsto_of_abs_tstat_shiftedNormal
    (μ := μ) (T := T) (crit := crit) (delta := delta) hAbs

/-- Reusable one-sided local-power bridge from a shifted-normal t limit.

If the t statistic converges to `N(δ, 1)` under a local alternative, then the
one-sided rejection probability for `{Tₙ > c}` converges to the shifted-normal
upper-tail probability. -/
theorem tTest_oneSidedLocalPower_tendsto_of_tstat_shiftedNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {crit delta : ℝ}
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x)
      (fun _ => μ) (gaussianReal delta 1)) :
    Tendsto (fun n => μ {ω | crit < T n ω}) atTop
      (𝓝 ((gaussianReal delta 1) (Set.Ioi crit))) := by
  have hfrontier :
      ((gaussianReal delta 1).map (fun x : ℝ => x)) (frontier (Set.Ioi crit)) = 0 := by
    simpa using normal_frontier_Ioi_null delta crit
  have h := TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
    hT (E := Set.Ioi crit) measurableSet_Ioi hfrontier
  have hmap : (gaussianReal delta 1).map (fun x : ℝ => x) = gaussianReal delta 1 := by
    simp
  simpa only [Set.mem_Ioi, hmap] using h

/-- **Hansen Theorem 9.1, asymptotic-size half, for the ordinary-OLS HC0 t-test.**

The two-sided HC0 t-test "reject if `|T| > c`" has asymptotic rejection
probability equal to the absolute-standard-normal mass of `(c, ∞)` — that is,
`P[|Z| > c] = 2(1 - Φ(c))` for `Z ∼ N(0, 1)`.

Scope and faithfulness notes:
* This formalizes only claim (b) of Hansen Theorem 9.1 (the rejection-probability
  limit). Claim (a), `T(θ₀) →d N(0, 1)`, is Hansen Theorem 7.11 and is reused
  via `olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal`. Claim (c),
  "the test has asymptotic size `α`", is the calibrated wrapper
  `olsHC0LinTTest_rejectionProb_tendsto_alpha`.
* The hypotheses are `RobustCovarianceConsistencyConditions` plus the
  score-weight bounded-in-probability conditions. That package is documented as
  *stronger* than Hansen's bare Assumption 7.2 (it adds iid-type conditions on
  the score outer products); it is the standard Chapter 7 robust-inference
  hypothesis stack, not a literal rendering of Assumptions 7.2/7.3.
* The t-statistic is evaluated at the true coefficient vector `β`, so the null
  `H₀ : θ = θ₀` holds by construction (`θ₀ = R'β`). The statement is therefore
  Theorem 9.1's conclusion *under* `H₀`; it is not a decision rule that
  discriminates `H₀` from an alternative. -/
theorem olsHC0LinTTest_rejectionProb_tendsto
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
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (crit : ℝ) :
    Tendsto
      (fun n => μ {ω | crit <
        |olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Ioi crit))) :=
  tTest_rejectionProb_tendsto_of_abs_tstat
    (olsHC0LinTStatOrZero_abs_tendstoInDistribution_standardNormalAbs
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

/-- **Hansen Theorem 9.1, explicit asymptotic-size `α` wrapper, for the ordinary-OLS HC0
t-test.**

This is the same rejection-probability conclusion as
`olsHC0LinTTest_rejectionProb_tendsto`, with the critical value calibrated so
that the absolute-standard-normal upper-tail mass is `α`. -/
theorem olsHC0LinTTest_rejectionProb_tendsto_alpha
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
      linearRestrictionStdError R (heteroAsymCov μ X e))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        |olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))|})
      atTop
      (𝓝 alpha) := by
  simpa [hcrit] using
    olsHC0LinTTest_rejectionProb_tendsto
      (μ := μ) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos crit

/-- The chi-square law has no atom at the frontier of `(c, ∞)`. -/
private theorem chiSquared_frontier_Ioi_null (q : ℕ) (crit : ℝ) :
    (chiSquared q) (frontier (Set.Ioi crit)) = 0 := by
  haveI : NoAtoms (chiSquared q) := instNoAtomsChiSquared q
  rw [frontier_Ioi]
  exact measure_singleton crit

/-- Generic Chapter 9 rejection-probability bridge for chi-square tests.

If a nonnegative Wald, minimum-distance, score, or Hausman statistic converges in
distribution to `χ²(q)`, then the probability of the rejection region
`{Wₙ > c}` converges to the `χ²(q)` upper-tail mass. -/
theorem chiSquaredTest_rejectionProb_tendsto_of_stat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : ℕ → Ω → ℝ} {q : ℕ} [Fact (0 < q)] {crit : ℝ}
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x)
      (fun _ => μ) (chiSquared q)) :
    Tendsto (fun n => μ {ω | crit < W n ω}) atTop
      (𝓝 ((chiSquared q) (Set.Ioi crit))) := by
  have hfrontier :
      ((chiSquared q).map (fun x : ℝ => x)) (frontier (Set.Ioi crit)) = 0 := by
    simpa using chiSquared_frontier_Ioi_null q crit
  have h := TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
    hW (E := Set.Ioi crit) measurableSet_Ioi
    hfrontier
  have hmap : (chiSquared q).map (fun x : ℝ => x) = chiSquared q := by
    simp
  simpa only [Set.mem_Ioi, hmap] using h

/-- Size-`α` wrapper for `chiSquaredTest_rejectionProb_tendsto_of_stat`.

If the chi-square critical value is calibrated so that the upper-tail mass is
`α`, then the rejection probability converges to `α`. -/
theorem chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : ℕ → Ω → ℝ} {q : ℕ} [Fact (0 < q)] {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared q) (Set.Ioi crit) = alpha)
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x)
      (fun _ => μ) (chiSquared q)) :
    Tendsto (fun n => μ {ω | crit < W n ω}) atTop (𝓝 alpha) := by
  have hlim :=
    chiSquaredTest_rejectionProb_tendsto_of_stat
      (μ := μ) (W := W) (q := q) (crit := crit) hW
  rw [hcrit] at hlim
  exact hlim

/-- Nonlinear OLS Wald test, calibrated size-`α` form for Hansen Theorems 9.2/9.3. -/
theorem nonlinearOlsWaldTest_rejectionProb_tendsto_alpha
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {r : ℕ} [Fact (0 < r)]
    {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (rfun : (k → ℝ) → (Fin r → ℝ)) (θ0 : Fin r → ℝ)
    {root : ℕ → ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {Z : Ω' → EuclideanSpace ℝ (Fin r)}
    {Vtheta : Matrix (Fin r) (Fin r) ℝ}
    (hT : TendstoInDistribution
      (fun n ω =>
        root n •
          (rfun (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)) - θ0))
      atTop (fun ω i => (Z ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hZ : HasLaw Z (multivariateGaussian 0 Vtheta) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (Rhat n ω)ᵀ * Vhat n ω * Rhat n ω) μ)
    (hV : TendstoInMeasure μ
      (fun n ω => (Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)
      atTop (fun _ => Vtheta))
    (hV_posDef : Vtheta.PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        nonlinearOlsWaldStatOrZero rfun θ0 (Rhat n ω) (Vhat n ω)
          (stackRegressors X n ω) (stackOutcomes y n ω) (root n)})
      atTop (𝓝 alpha) := by
  have hW :=
    nonlinearOlsWaldStatOrZero_tendstoInDistribution_chiSquared
      (μ := μ) (ν := ν) (r := r) (X := X) (y := y)
      rfun θ0 (root := root) (Rhat := Rhat) (Vhat := Vhat)
      (Z := Z) (Vtheta := Vtheta)
      hT hZ hV_meas hV hV_posDef
  exact chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ)
    (W := fun n ω =>
      nonlinearOlsWaldStatOrZero rfun θ0 (Rhat n ω) (Vhat n ω)
        (stackRegressors X n ω) (stackOutcomes y n ω) (root n))
    (q := r) (crit := crit) (alpha := alpha) hcrit hW

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.2, nonlinear OLS Wald test from Chapter 7.**

This is the theorem-facing robust nonlinear Wald wrapper. The restriction-gap
Gaussian limit is supplied by Chapter 7's nonlinear Delta-method wrapper, and
the plug-in restriction covariance is supplied by Chapter 7's transposed
nonlinear derivative covariance wrapper. The differentiability/Taylor
remainder and Gaussian image-law premises are the corresponding Chapter 7
inputs, not new Chapter 9 CLT assumptions. -/
theorem nonlinearOlsWaldTest_rejectionProb_tendsto_alpha_of_chapter7
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (rfun : (k → ℝ) → (Fin r → ℝ)) (θ0 : Fin r → ℝ)
    (Rfun : (k → ℝ) → Matrix k (Fin r) ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hY_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (n : ℝ) •
            (rfun (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)) - θ0)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hrem :
      TendstoInMeasure μ
        (fun (n : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (n : ℝ) •
              (rfun (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) - θ0)) :
            EuclideanSpace ℝ (Fin r)) -
            matrixContinuousLinearMap (Rfun β)ᵀ
              (WithLp.toLp 2
                (Real.sqrt (n : ℝ) •
                  (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))))
        atTop (fun _ => 0))
    (hLimitLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          matrixContinuousLinearMap (Rfun β)ᵀ
            (WithLp.toLp 2 ((popGram μ X)⁻¹ *ᵥ z.ofLp)))
        (multivariateGaussian 0 ((Rfun β)ᵀ * heteroAsymCov μ X e * Rfun β))
        (multivariateGaussian 0 (scoreCovMat μ X e)))
    (hRfun : ContinuousAt Rfun β)
    (hR_meas : ∀ n, AEStronglyMeasurable
      (fun ω => Rfun
        (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω))) μ)
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => heteroAsymCov μ X e))
    (hV_posDef : ((Rfun β)ᵀ * heteroAsymCov μ X e * Rfun β).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        nonlinearOlsWaldStatOrZero rfun θ0
          (Rfun (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))
          (Vhat n ω)
          (stackRegressors X n ω) (stackOutcomes y n ω)
          (Real.sqrt (n : ℝ))})
      atTop (𝓝 alpha) := by
  let Vtheta : Matrix (Fin r) (Fin r) ℝ :=
    (Rfun β)ᵀ * heteroAsymCov μ X e * Rfun β
  have hT := nonlinearRestrictionGap_olsBetaOrZero_delta_tendstoInDistribution_gaussian
    (μ := μ) (X := X) (e := e) (y := y) (q := Fin r)
    h β rfun θ0 (Rfun β)ᵀ hmodel hY_meas hrem hLimitLaw
  have hVtheta := nonlinearDerivativeCovarianceTranspose_olsBetaOrZero_tendstoInMeasure
    (μ := μ) (X := X) (e := e) (y := y) β
    h.toLeastSquaresConsistencyConditions hmodel Rfun hRfun hR_meas hV_meas hV
  have hRV_meas : ∀ n, AEStronglyMeasurable
      (fun ω =>
        (Rfun (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)))ᵀ *
          Vhat n ω *
          Rfun (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω))) μ := by
    intro n
    have hRT_meas : AEStronglyMeasurable
        (fun ω =>
          (Rfun (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))ᵀ) μ :=
      (continuous_id.matrix_transpose).comp_aestronglyMeasurable (hR_meas n)
    have hleft : AEStronglyMeasurable
        (fun ω =>
          (Rfun (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))ᵀ * Vhat n ω) μ := by
      have hprod := hRT_meas.prodMk (hV_meas n)
      exact (continuous_fst.matrix_mul continuous_snd).comp_aestronglyMeasurable hprod
    have hprod := hleft.prodMk (hR_meas n)
    exact (continuous_fst.matrix_mul continuous_snd).comp_aestronglyMeasurable hprod
  have hZ : HasLaw
      (fun z : EuclideanSpace ℝ (Fin r) => z)
      (multivariateGaussian 0 Vtheta)
      (multivariateGaussian 0 Vtheta) := by
    simpa [id] using (HasLaw.id (μ := multivariateGaussian 0 Vtheta))
  exact nonlinearOlsWaldTest_rejectionProb_tendsto_alpha
    (μ := μ) (ν := multivariateGaussian 0 Vtheta)
    (r := r) (X := X) (y := y)
    rfun θ0
    (root := fun n => Real.sqrt (n : ℝ))
    (Rhat := fun n ω =>
      Rfun (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)))
    (Vhat := Vhat)
    (Z := fun z : EuclideanSpace ℝ (Fin r) => z)
    (Vtheta := Vtheta)
    (by simpa [Vtheta] using hT)
    hZ hRV_meas (by simpa [Vtheta] using hVtheta)
    (by simpa [Vtheta] using hV_posDef) hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.3, nonlinear homoskedastic OLS Wald test from Chapter 7.**

The homoskedastic statistic uses the same Chapter 7 nonlinear Delta-method
limit together with Chapter 7's homoskedastic-to-sandwich covariance bridge.
The equality premise is normally provided by
`homoAsymCov_eq_heteroAsymCov` or one of its Chapter 7 homoskedastic wrappers. -/
theorem nonlinearOlsHomoWaldTest_rejectionProb_tendsto_alpha_of_chapter7
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (rfun : (k → ℝ) → (Fin r → ℝ)) (θ0 : Fin r → ℝ)
    (Rfun : (k → ℝ) → Matrix k (Fin r) ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hY_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (n : ℝ) •
            (rfun (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)) - θ0)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hrem :
      TendstoInMeasure μ
        (fun (n : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (n : ℝ) •
              (rfun (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) - θ0)) :
            EuclideanSpace ℝ (Fin r)) -
            matrixContinuousLinearMap (Rfun β)ᵀ
              (WithLp.toLp 2
                (Real.sqrt (n : ℝ) •
                  (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))))
        atTop (fun _ => 0))
    (hLimitLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          matrixContinuousLinearMap (Rfun β)ᵀ
            (WithLp.toLp 2 ((popGram μ X)⁻¹ *ᵥ z.ofLp)))
        (multivariateGaussian 0 ((Rfun β)ᵀ * heteroAsymCov μ X e * Rfun β))
        (multivariateGaussian 0 (scoreCovMat μ X e)))
    (hRfun : ContinuousAt Rfun β)
    (hR_meas : ∀ n, AEStronglyMeasurable
      (fun ω => Rfun
        (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω))) μ)
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => homoAsymCov μ X e))
    (hVeq : homoAsymCov μ X e = heteroAsymCov μ X e)
    (hV_posDef : ((Rfun β)ᵀ * homoAsymCov μ X e * Rfun β).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        nonlinearOlsWaldStatOrZero rfun θ0
          (Rfun (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))
          (Vhat n ω)
          (stackRegressors X n ω) (stackOutcomes y n ω)
          (Real.sqrt (n : ℝ))})
      atTop (𝓝 alpha) := by
  have hV_hetero :
      TendstoInMeasure μ Vhat atTop (fun _ => heteroAsymCov μ X e) := by
    simpa [← hVeq] using hV
  exact nonlinearOlsWaldTest_rejectionProb_tendsto_alpha_of_chapter7
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β rfun θ0 Rfun hmodel hY_meas hrem hLimitLaw
    hRfun hR_meas hV_meas hV_hetero
    (by simpa [← hVeq] using hV_posDef) hcrit

/-- Reusable efficient-MD nonlinear criterion-test bridge from a supplied limit law. -/
theorem emdJTest_rejectionProb_tendsto_alpha_of_limitLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {df : ℕ} [Fact (0 < df)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    {Z : Ω' → k → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (hDiff : TendstoInDistribution (fun n ω => root n • (bhat n ω - btilde n ω))
      atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω)) (chiSquared df) ν)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        emdJStatOrZero (Vhat n ω) (bhat n ω) (btilde n ω) (root n)})
      atTop (𝓝 alpha) := by
  have hJ :=
    emdJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := μ) (ν := ν) (df := df) (bhat := bhat) (btilde := btilde)
      (root := root) (Z := Z) (Vhat := Vhat) (V := V)
      hDiff hV_meas hV hV_nonsing hLaw
  exact chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ)
    (W := fun n ω => emdJStatOrZero (Vhat n ω) (bhat n ω) (btilde n ω) (root n))
    (q := df) (crit := crit) (alpha := alpha) hcrit hJ

/-- Reusable CLS nonlinear criterion-test bridge from a supplied limit law. -/
theorem clsJTest_rejectionProb_tendsto_alpha_of_limitLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {df : ℕ} [Fact (0 < df)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    {Z : Ω' → k → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (hDiff : TendstoInDistribution (fun n ω => root n • (bhat n ω - btilde n ω))
      atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω)) (chiSquared df) ν)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        clsJStatOrZero (Vhat n ω) (bhat n ω) (btilde n ω) (root n)})
      atTop (𝓝 alpha) := by
  have hJ :=
    clsJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := μ) (ν := ν) (df := df) (bhat := bhat) (btilde := btilde)
      (root := root) (Z := Z) (Vhat := Vhat) (V := V)
      hDiff hV_meas hV hV_nonsing hLaw
  exact chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ)
    (W := fun n ω => clsJStatOrZero (Vhat n ω) (bhat n ω) (btilde n ω) (root n))
    (q := df) (crit := crit) (alpha := alpha) hcrit hJ

omit [DecidableEq k] in
/-- Reusable nonlinear Hausman-test bridge from a supplied matrix limit and limit law. -/
theorem nonlinearHausmanTest_rejectionProb_tendsto_alpha_of_matrixLimit
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {r df : ℕ} [Fact (0 < df)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {Z : Ω' → k → ℝ}
    {A : Matrix k k ℝ}
    (hDiff : TendstoInDistribution (fun n ω => root n • (bhat n ω - btilde n ω))
      atTop Z (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable
      (fun ω => Rhat n ω * ((Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)⁻¹ * (Rhat n ω)ᵀ) μ)
    (hA : TendstoInMeasure μ
      (fun n ω => Rhat n ω * ((Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)⁻¹ * (Rhat n ω)ᵀ)
      atTop (fun _ => A))
    (hLaw : HasLaw (fun ω => Z ω ⬝ᵥ (A *ᵥ Z ω)) (chiSquared df) ν)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        nonlinearHausmanStatOrZero (Rhat n ω) (Vhat n ω)
          (bhat n ω) (btilde n ω) (root n)})
      atTop (𝓝 alpha) := by
  have hH :=
    nonlinearHausmanStatOrZero_tendstoInDistribution_chiSquared_of_matrixLimit
      (μ := μ) (ν := ν) (r := r) (df := df)
      (bhat := bhat) (btilde := btilde) (root := root)
      (Rhat := Rhat) (Vhat := Vhat) (Z := Z) (A := A)
      hDiff hA_meas hA hLaw
  exact chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ)
    (W := fun n ω =>
      nonlinearHausmanStatOrZero (Rhat n ω) (Vhat n ω)
        (bhat n ω) (btilde n ω) (root n))
    (q := df) (crit := crit) (alpha := alpha) hcrit hH

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.4, efficient-MD nonlinear criterion test from Chapter 8.**

This theorem-facing wrapper obtains the scaled unrestricted-minus-constrained
estimator limit and the limiting criterion quadratic law from Chapter 8, then
applies the reusable Chapter 9 criterion-test bridge. -/
theorem emdJTest_rejectionProb_tendsto_alpha_of_chapter8
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : Type*} [Fintype q] [DecidableEq q] [Fact (0 < Fintype.card q)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β V⁻¹ R
      (fun n ω => root n • (bhat n ω - β)))
    (hT : GaussianLimit μ (fun n ω => root n • (bhat n ω - β)) V)
    (hV_posDef : V.PosDef)
    (hR_full : Function.Injective R.mulVec)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card q)) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        emdJStatOrZero (Vhat n ω) (bhat n ω) (btilde n ω) (root n)})
      atTop (𝓝 alpha) := by
  have hDiff :=
    unrestrictedSubConstrainedEstimator_efficientDifference_tendstoInDistribution_multivariateGaussian
    (μ := μ) (root := root) (bhat := bhat) (btilde := btilde)
    (β := β) (R := R) (V := V) hlinear hT (posDef_det_isUnit V hV_posDef)
  have hLaw :=
    emdDifferenceCriterionQuadratic_hasLaw_chiSquared R V hV_posDef hR_full
  exact emdJTest_rejectionProb_tendsto_alpha_of_limitLaw
    (μ := μ) (ν := multivariateGaussian 0 (emdDifferenceAsymptoticVariance R V))
    (df := Fintype.card q)
    (bhat := bhat) (btilde := btilde) (root := root)
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    (Vhat := Vhat) (V := V)
    hDiff hV_meas hV (posDef_det_isUnit V hV_posDef) hLaw
    hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.5, CLS nonlinear criterion test from Chapter 8.**

This has the same formal shape as the EMD wrapper, but is named separately for
Hansen's CLS criterion surface. The constrained-estimator difference limit and
criterion quadratic law are composed from Chapter 8 rather than assumed
directly in Chapter 9. -/
theorem clsJTest_rejectionProb_tendsto_alpha_of_chapter8
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : Type*} [Fintype q] [DecidableEq q] [Fact (0 < Fintype.card q)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β V⁻¹ R
      (fun n ω => root n • (bhat n ω - β)))
    (hT : GaussianLimit μ (fun n ω => root n • (bhat n ω - β)) V)
    (hV_posDef : V.PosDef)
    (hR_full : Function.Injective R.mulVec)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card q)) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        clsJStatOrZero (Vhat n ω) (bhat n ω) (btilde n ω) (root n)})
      atTop (𝓝 alpha) := by
  have hDiff :=
    unrestrictedSubConstrainedEstimator_efficientDifference_tendstoInDistribution_multivariateGaussian
    (μ := μ) (root := root) (bhat := bhat) (btilde := btilde)
    (β := β) (R := R) (V := V) hlinear hT (posDef_det_isUnit V hV_posDef)
  have hLaw :=
    emdDifferenceCriterionQuadratic_hasLaw_chiSquared R V hV_posDef hR_full
  exact clsJTest_rejectionProb_tendsto_alpha_of_limitLaw
    (μ := μ) (ν := multivariateGaussian 0 (emdDifferenceAsymptoticVariance R V))
    (df := Fintype.card q)
    (bhat := bhat) (btilde := btilde) (root := root)
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    (Vhat := Vhat) (V := V)
    hDiff hV_meas hV (posDef_det_isUnit V hV_posDef) hLaw
    hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.7, nonlinear Hausman test from Chapter 8.**

The estimator-difference limit is obtained from Chapter 8's constrained
estimator theorem; the Hausman plug-in matrix limit and limiting quadratic
law are also supplied by Chapter 8. Chapter 9 only assembles the statistic and
rejection-probability bridge. -/
theorem nonlinearHausmanTest_rejectionProb_tendsto_alpha_of_chapter8
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {r : ℕ} [Fact (0 < r)]
    {bhat btilde : ℕ → Ω → k → ℝ} {root : ℕ → ℝ}
    (β : k → ℝ) (R : Matrix k (Fin r) ℝ) (V : Matrix k k ℝ)
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β V⁻¹ R
      (fun n ω => root n • (bhat n ω - β)))
    (hT : GaussianLimit μ (fun n ω => root n • (bhat n ω - β)) V)
    (hV_posDef : V.PosDef)
    (hR_full : Function.Injective R.mulVec)
    (hRhat : MatrixEstimatorConsistent μ Rhat R)
    (hVhat : CovarianceEstimatorConsistent μ Vhat V)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        nonlinearHausmanStatOrZero (Rhat n ω) (Vhat n ω)
          (bhat n ω) (btilde n ω) (root n)})
      atTop (𝓝 alpha) := by
  haveI : Fact (0 < Fintype.card (Fin r)) := ⟨by simpa using (Fact.out : 0 < r)⟩
  have hDiff :=
    unrestrictedSubConstrainedEstimator_efficientDifference_tendstoInDistribution_multivariateGaussian
    (μ := μ) (root := root) (bhat := bhat) (btilde := btilde)
    (β := β) (R := R) (V := V) hlinear hT (posDef_det_isUnit V hV_posDef)
  have hA_meas : ∀ n, AEStronglyMeasurable
      (fun ω => Rhat n ω * ((Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)⁻¹ *
        (Rhat n ω)ᵀ) μ := by
    intro n
    simpa [hausmanQuadraticMatrix] using
      hausmanQuadraticMatrix_aestronglyMeasurable_of_estimatedRestriction
        (Rhat n) (Vhat n) (hRhat.matrix_measurable n) (hVhat.covariance_measurable n)
  have hA : TendstoInMeasure μ
      (fun n ω => Rhat n ω * ((Rhat n ω)ᵀ * Vhat n ω * Rhat n ω)⁻¹ *
        (Rhat n ω)ᵀ)
      atTop (fun _ => hausmanQuadraticMatrix R V) := by
    simpa [hausmanQuadraticMatrix] using
      hausmanQuadraticMatrix_tendstoInMeasure_of_estimatedRestriction
        hRhat hVhat (restrictionCov_det_isUnit_of_cov_posDef V R hV_posDef hR_full)
  have hLaw :=
    emdDifferenceHausmanQuadratic_hasLaw_chiSquared R V hV_posDef hR_full
  exact nonlinearHausmanTest_rejectionProb_tendsto_alpha_of_matrixLimit
    (μ := μ) (ν := multivariateGaussian 0 (emdDifferenceAsymptoticVariance R V))
    (r := r) (df := r) (bhat := bhat) (btilde := btilde) (root := root)
    (Rhat := Rhat) (Vhat := Vhat)
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp) (A := hausmanQuadraticMatrix R V)
    hDiff hA_meas hA
    (by simpa [Fintype.card_fin] using hLaw)
    hcrit

/-- The scaled chi-square law `χ²(q) / q` has no atom at the frontier of `(c, ∞)`. -/
private theorem chiSquaredDivDegrees_frontier_Ioi_null
    (q : ℕ) [Fact (0 < q)] (crit : ℝ) :
    (chiSquaredDivDegrees q) (frontier (Set.Ioi crit)) = 0 := by
  rw [chiSquaredDivDegrees, frontier_Ioi]
  rw [Measure.map_apply (by fun_prop : Measurable fun x : ℝ => x / (q : ℝ))
    (measurableSet_singleton crit)]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : 0 < q)
  have hqne : (q : ℝ) ≠ 0 := hqpos.ne'
  have hpre_subset :
      (fun x : ℝ => x / (q : ℝ)) ⁻¹' ({crit} : Set ℝ) ⊆
        ({crit * (q : ℝ)} : Set ℝ) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [Set.mem_singleton_iff]
    calc
      x = x / (q : ℝ) * (q : ℝ) := (div_mul_cancel₀ x hqne).symm
      _ = crit * (q : ℝ) := by rw [hx]
  haveI : NoAtoms (chiSquared q) := instNoAtomsChiSquared q
  exact measure_mono_null hpre_subset (measure_singleton (crit * (q : ℝ)))

/-- Generic Chapter 9 rejection-probability bridge for F-test limits.

If an F statistic converges in distribution to `χ²(q) / q`, then the rejection
probability of the rule `{Fₙ > c}` converges to the corresponding scaled
chi-square upper-tail mass. -/
theorem fTest_rejectionProb_tendsto_of_stat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Fstat : ℕ → Ω → ℝ} {q : ℕ} [Fact (0 < q)] {crit : ℝ}
    (hF : TendstoInDistribution Fstat atTop (fun x : ℝ => x)
      (fun _ => μ) (chiSquaredDivDegrees q)) :
    Tendsto (fun n => μ {ω | crit < Fstat n ω}) atTop
      (𝓝 ((chiSquaredDivDegrees q) (Set.Ioi crit))) := by
  have hfrontier :
      ((chiSquaredDivDegrees q).map (fun x : ℝ => x)) (frontier (Set.Ioi crit)) = 0 := by
    simpa using chiSquaredDivDegrees_frontier_Ioi_null q crit
  have h := TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
    hF (E := Set.Ioi crit) measurableSet_Ioi hfrontier
  have hmap : (chiSquaredDivDegrees q).map (fun x : ℝ => x) =
      chiSquaredDivDegrees q := by
    simp
  simpa only [Set.mem_Ioi, hmap] using h

/-- Size-`α` wrapper for `fTest_rejectionProb_tendsto_of_stat`. -/
theorem fTest_rejectionProb_tendsto_alpha_of_stat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Fstat : ℕ → Ω → ℝ} {q : ℕ} [Fact (0 < q)] {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquaredDivDegrees q) (Set.Ioi crit) = alpha)
    (hF : TendstoInDistribution Fstat atTop (fun x : ℝ => x)
      (fun _ => μ) (chiSquaredDivDegrees q)) :
    Tendsto (fun n => μ {ω | crit < Fstat n ω}) atTop (𝓝 alpha) := by
  have hlim :=
    fTest_rejectionProb_tendsto_of_stat
      (μ := μ) (Fstat := Fstat) (q := q) (crit := crit) hF
  rw [hcrit] at hlim
  exact hlim

/-- Hansen Definition 9.4: a real statistic diverges to `+∞` in probability.

The codomain is `ℝ≥0∞`, matching Lean's measure-valued probabilities. -/
def TendstoInProbabilityAtTop (μ : Measure Ω) (T : ℕ → Ω → ℝ) : Prop :=
  ∀ M : ℝ, Tendsto (fun n => μ {ω | T n ω ≤ M}) atTop (𝓝 (0 : ℝ≥0∞))

/-- Constructor for Hansen's `Tₙ →p +∞` notion from eventual almost-sure lower bounds.

This is the fixed-alternative divergence step used by Theorems 9.8 and 9.9:
to prove divergence in probability it is enough to show that, for every finite
threshold `M`, the statistic eventually exceeds `M` almost surely. -/
theorem tendstoInProbabilityAtTop_of_eventually_ae_gt
    {μ : Measure Ω} {T : ℕ → Ω → ℝ}
    (hT : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, M < T n ω) :
    TendstoInProbabilityAtTop μ T := by
  intro M
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hT M] with n hn
  have hzero : μ {ω | T n ω ≤ M} = 0 := by
    have hbad : μ {ω | ¬ M < T n ω} = 0 := by
      simpa [ae_iff] using hn
    simpa [not_lt] using hbad
  rw [hzero]

/-- Reusable divergence constructor for scalar two-sided t statistics. -/
theorem abs_tstat_tendstoInProbabilityAtTop_of_eventually_ae_gt
    {μ : Measure Ω} {T : ℕ → Ω → ℝ}
    (hT : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, M < |T n ω|) :
    TendstoInProbabilityAtTop μ (fun n ω => |T n ω|) :=
  tendstoInProbabilityAtTop_of_eventually_ae_gt (μ := μ) hT

/-- Reusable divergence constructor for Wald statistics. -/
theorem waldStat_tendstoInProbabilityAtTop_of_eventually_ae_gt
    {μ : Measure Ω} {W : ℕ → Ω → ℝ}
    (hW : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, M < W n ω) :
    TendstoInProbabilityAtTop μ W :=
  tendstoInProbabilityAtTop_of_eventually_ae_gt (μ := μ) hW

/-- Generic consistency bridge for upper-tail tests.

If `Tₙ →p +∞`, then for any fixed finite critical value `c`, the rejection
probability of the rule `{Tₙ > c}` tends to one. -/
theorem rejectionProb_tendsto_one_of_tendstoInProbabilityAtTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {crit : ℝ}
    (hmeas : ∀ n, NullMeasurableSet {ω | T n ω ≤ crit} μ)
    (hT : TendstoInProbabilityAtTop μ T) :
    Tendsto (fun n => μ {ω | crit < T n ω}) atTop (𝓝 (1 : ℝ≥0∞)) := by
  have hbad := hT crit
  have hEq :
      (fun n => μ {ω | crit < T n ω}) =
        fun n => 1 - μ {ω | T n ω ≤ crit} := by
    funext n
    have hcompl : {ω | crit < T n ω} = ({ω | T n ω ≤ crit} : Set Ω)ᶜ := by
      ext ω
      simp [not_le]
    rw [hcompl, prob_compl_eq_one_sub₀ (μ := μ)
      (s := {ω | T n ω ≤ crit}) (hmeas n)]
  rw [hEq]
  simpa using
    ENNReal.Tendsto.sub tendsto_const_nhds hbad
      (Or.inl (by simp : (1 : ℝ≥0∞) ≠ ∞))

/-- Reusable consistency bridge for two-sided t tests.

Once the absolute t statistic diverges to `+∞` in probability under a fixed
alternative, every fixed two-sided rejection threshold is crossed with
probability tending to one. The model-specific proof of `|Tₙ| →p +∞` remains a
separate premise. -/
theorem tTest_consistent_of_abs_tstat_tendstoInProbabilityAtTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {crit : ℝ}
    (hmeas : ∀ n, NullMeasurableSet {ω | |T n ω| ≤ crit} μ)
    (hT : TendstoInProbabilityAtTop μ (fun n ω => |T n ω|)) :
    Tendsto (fun n => μ {ω | crit < |T n ω|}) atTop (𝓝 (1 : ℝ≥0∞)) :=
  rejectionProb_tendsto_one_of_tendstoInProbabilityAtTop
    (μ := μ) (T := fun n ω => |T n ω|) (crit := crit) hmeas hT

/-- Reusable consistency bridge for Wald tests.

Once a Wald statistic diverges to `+∞` in probability under a fixed
alternative, every fixed upper-tail rejection threshold is crossed with
probability tending to one. The model-specific proof of `Wₙ →p +∞` remains a
separate premise. -/
theorem waldTest_consistent_of_stat_tendstoInProbabilityAtTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : ℕ → Ω → ℝ} {crit : ℝ}
    (hmeas : ∀ n, NullMeasurableSet {ω | W n ω ≤ crit} μ)
    (hW : TendstoInProbabilityAtTop μ W) :
    Tendsto (fun n => μ {ω | crit < W n ω}) atTop (𝓝 (1 : ℝ≥0∞)) :=
  rejectionProb_tendsto_one_of_tendstoInProbabilityAtTop
    (μ := μ) (T := W) (crit := crit) hmeas hW

/-- Reusable abstract local-power bridge for Wald tests.

If a Wald statistic converges under a local alternative to a real limit law `ν`
whose upper-tail frontier has zero mass, then the rejection probability of
`{Wₙ > c}` converges to the upper-tail mass of `ν`. This is stated with an
abstract `ν` so the same bridge can be reused for any real upper-tail limit;
`waldTest_localPower_tendsto_noncentralChiSquared` below instantiates it with
the named noncentral chi-square law. -/
theorem waldTest_localPower_tendsto_of_stat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {W : ℕ → Ω → ℝ} {crit : ℝ}
    (hfrontier : ν (frontier (Set.Ioi crit)) = 0)
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => μ) ν) :
    Tendsto (fun n => μ {ω | crit < W n ω}) atTop (𝓝 (ν (Set.Ioi crit))) := by
  have hfrontier' :
      (ν.map (fun x : ℝ => x)) (frontier (Set.Ioi crit)) = 0 := by
    simpa using hfrontier
  have h := TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
    hW (E := Set.Ioi crit) measurableSet_Ioi hfrontier'
  have hmap : (ν.map (fun x : ℝ => x)) (Set.Ioi crit) = ν (Set.Ioi crit) := by
    simp
  simpa only [Set.mem_Ioi, hmap] using h

/-- Reusable local-power bridge for the named noncentral chi-square law.

Once the local-alternative Wald statistic has the noncentral chi-square limit
given by `restrictionWaldStatOrZero_tendstoInDistribution_noncentralChiSquared`,
the upper-tail rejection probability converges to the corresponding noncentral
chi-square tail probability. The frontier-null premise is the only analytic
regularity fact needed to apply the portmanteau rejection-set bridge. -/
theorem waldTest_localPower_tendsto_noncentralChiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : ℕ → Ω → ℝ} {r : ℕ} {mean : Fin r → ℝ}
    {V : Matrix (Fin r) (Fin r) ℝ} {crit : ℝ}
    (hfrontier : (noncentralChiSquared r mean V) (frontier (Set.Ioi crit)) = 0)
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x)
      (fun _ => μ) (noncentralChiSquared r mean V)) :
    Tendsto (fun n => μ {ω | crit < W n ω}) atTop
      (𝓝 ((noncentralChiSquared r mean V) (Set.Ioi crit))) :=
  waldTest_localPower_tendsto_of_stat
    (μ := μ) (ν := noncentralChiSquared r mean V) (W := W) (crit := crit)
    hfrontier hW

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.2, robust multivariate Wald test, asymptotic-size `α` form.**

For a linear hypothesis encoded by `R`, the ordinary-OLS HC0 Wald rule
"reject if `W > c`" has rejection probability tending to `α` when the critical
value has `χ²(r)` upper-tail mass `α`. The null is encoded by centering at the
true coefficient vector `β`; the hypotheses reuse Chapter 7's robust feasible
HC moment package, which is stronger than Hansen's bare Assumptions 7.2--7.4. -/
theorem linMap_olsHC0WaldTest_rejectionProb_tendsto_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        linMapOlsWaldStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))})
      atTop (𝓝 alpha) := by
  have hW :=
    linMap_olsHC0WaldStatOrZero_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      β R hm hV_posDef
  have hlim :=
    chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
      (μ := μ) (q := r) (crit := crit) (alpha := alpha) hcrit hW
  simpa [linMapOlsWaldStatOrZero] using hlim

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.3, homoskedastic multivariate Wald test, asymptotic-size `α` form.**

For a linear hypothesis encoded by `R`, the ordinary-OLS homoskedastic Wald rule
"reject if `W⁰ > c`" has rejection probability tending to `α` when the critical
value has `χ²(r)` upper-tail mass `α`. The statement reuses Chapter 7's
homoskedastic Wald limit and the iid robust feasible HC package used there. -/
theorem linMap_olsHomoWaldTest_rejectionProb_tendsto_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : IidRobustFeasibleHCMomentConditions μ X e y β)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        linMapOlsWaldStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))})
      atTop (𝓝 alpha) := by
  have hW :=
    linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared_of_iidRobustFeasibleHC
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      β R hm hX0 hhomo hV_posDef
  have hlim :=
    chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
      (μ := μ) (q := r) (crit := crit) (alpha := alpha) hcrit hW
  simpa [linMapOlsWaldStatOrZero] using hlim

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.4, linear efficient minimum-distance test, asymptotic-size `α` form.**

This is the linear-hypothesis slice of the efficient minimum-distance test:
Hansen's deterministic identity `J* = W` reduces the rejection-probability
claim to the robust Wald wrapper. The general nonlinear criterion-statistic
wrapper is `emdJTest_rejectionProb_tendsto_alpha_of_limitLaw`. -/
theorem emdLinearJTest_rejectionProb_tendsto_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        emdLinearJStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))})
      atTop (𝓝 alpha) := by
  simpa [emdLinearJStatOrZero] using
    linMap_olsHC0WaldTest_rejectionProb_tendsto_alpha
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      β R hm hV_posDef hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.5, linear homoskedastic minimum-distance test,
asymptotic-size `α` form.**

This is the linear-hypothesis slice of the homoskedastic minimum-distance test:
Hansen's deterministic identity with the homoskedastic Wald statistic reduces
the rejection-probability claim to the homoskedastic Wald wrapper. The general
nonlinear criterion-statistic wrapper is
`clsJTest_rejectionProb_tendsto_alpha_of_limitLaw`. -/
theorem clsLinearJTest_rejectionProb_tendsto_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : IidRobustFeasibleHCMomentConditions μ X e y β)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        clsLinearJStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))})
      atTop (𝓝 alpha) := by
  simpa [clsLinearJStatOrZero] using
    linMap_olsHomoWaldTest_rejectionProb_tendsto_alpha
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      β R hm hX0 hhomo hV_posDef hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.6, linear F statistic, asymptotic `χ²(q) / q` law.**

For a linear hypothesis encoded by `R`, the homoskedastic F statistic is the
homoskedastic Wald statistic divided by the number of restrictions. Therefore
the Chapter 7 homoskedastic Wald limit implies the scaled chi-square limit
`χ²(r) / r`. The hypotheses reuse Chapter 7's iid robust feasible HC package
plus homoskedasticity, which is stronger than Hansen's bare asymptotic
assumption stack. -/
theorem linMap_olsHomoFStatOrZero_tendstoInDistribution_chiSquaredDivDegrees
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : IidRobustFeasibleHCMomentConditions μ X e y β)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun n ω =>
        linMapOlsFStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquaredDivDegrees r) := by
  have hW :=
    linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared_of_iidRobustFeasibleHC
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      β R hm hX0 hhomo hV_posDef
  have hFraw :
      TendstoInDistribution
        (fun n ω =>
          linMapOlsFStatOrZero R
            (olsHomoCovStar
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
        atTop (fun x : ℝ => x / (r : ℝ)) (fun _ => μ) (chiSquared r) := by
    simpa [Function.comp_def, linMapOlsFStatOrZero, linMapOlsWaldStatOrZero] using
      hW.continuous_comp (by fun_prop : Continuous fun x : ℝ => x / (r : ℝ))
  have hLaw :
      HasLaw (fun x : ℝ => x / (r : ℝ)) (chiSquaredDivDegrees r) (chiSquared r) := by
    exact ⟨by fun_prop, rfl⟩
  exact tendstoInDistribution_id_of_hasLaw_limit_real hFraw hLaw

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.6, linear F test, asymptotic-size `α` form.**

If the F critical value is calibrated against the `χ²(r) / r` upper-tail law,
then the homoskedastic OLS F-test rejection probability tends to `α`. -/
theorem linMap_olsHomoFTest_rejectionProb_tendsto_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : IidRobustFeasibleHCMomentConditions μ X e y β)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquaredDivDegrees r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        linMapOlsFStatOrZero R
          (olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))})
      atTop (𝓝 alpha) := by
  have hF :=
    linMap_olsHomoFStatOrZero_tendstoInDistribution_chiSquaredDivDegrees
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      β R hm hX0 hhomo hV_posDef
  exact fTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ) (Fstat := fun n ω =>
      linMapOlsFStatOrZero R
        (olsHomoCovStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
        (stackRegressors X n ω) (stackOutcomes y n ω) β
        (Real.sqrt (n : ℝ)))
    (q := r) (crit := crit) (alpha := alpha) hcrit hF

set_option linter.style.longLine false in
/-- **Hansen Theorem 9.7, linear Hausman/Wald equivalence slice,
asymptotic-size `α` form.**

For linear hypotheses the Hausman statistic reduces to the robust Wald
statistic. This theorem records the corresponding rejection-probability
conclusion. The general nonlinear statistic-level wrapper is
`nonlinearHausmanTest_rejectionProb_tendsto_alpha_of_matrixLimit`. -/
theorem linMap_olsHC0HausmanTest_rejectionProb_tendsto_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun n => μ {ω | crit <
        linMapOlsHausmanStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ))})
      atTop (𝓝 alpha) := by
  simpa [linMapOlsHausmanStatOrZero_eq_wald] using
    linMap_olsHC0WaldTest_rejectionProb_tendsto_alpha
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      β R hm hV_posDef hcrit

end HansenEconometrics
