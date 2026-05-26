import HansenEconometrics.Chapter7Asymptotics.Inference

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
* `linMap_olsHC0WaldTest_rejectionProb_tendsto_alpha` and
  `linMap_olsHomoWaldTest_rejectionProb_tendsto_alpha` — Theorems 9.2 and 9.3's
  rejection-probability/size-`α` conclusions for the Chapter 7 robust and
  homoskedastic multivariate Wald statistics.
* `emdLinearJTest_rejectionProb_tendsto_alpha` and
  `clsLinearJTest_rejectionProb_tendsto_alpha` — the linear-hypothesis
  minimum-distance testing slice of Theorems 9.4 and 9.5, using Hansen's
  deterministic identity between the EMD/CLS criterion statistics and the
  corresponding Wald statistics.
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
open scoped Matrix Real Topology ProbabilityTheory ENNReal

namespace HansenEconometrics

open Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {k : Type*} [Fintype k] [DecidableEq k]

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
theorem emdLinearJStatOrZero_eq_wald
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) :
    emdLinearJStatOrZero R Vhat X y β root =
      linMapOlsWaldStatOrZero R Vhat X y β root :=
  rfl

/-- Hansen's linear-hypothesis identity between homoskedastic MD and homoskedastic Wald tests. -/
theorem clsLinearJStatOrZero_eq_wald
    {r : ℕ} {n : Type*} [Fintype n] (R : Matrix (Fin r) k ℝ)
    (Vhat : Matrix k k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (β : k → ℝ) (root : ℝ) :
    clsLinearJStatOrZero R Vhat X y β root =
      linMapOlsWaldStatOrZero R Vhat X y β root :=
  rfl

/-- The absolute standard-normal law has no atom at the frontier of `(c, ∞)`.

The frontier of `Set.Ioi c` is the singleton `{c}`, exactly the frontier of
`Set.Iic c`, so this reduces to `standardNormalAbs_frontier_Iic_null`. -/
private theorem standardNormalAbs_frontier_Ioi_null (crit : ℝ) :
    ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (frontier (Set.Ioi crit)) = 0 := by
  have hfr : frontier (Set.Ioi crit) = frontier (Set.Iic crit) := by
    rw [frontier_Ioi, frontier_Iic]
  rw [hfr]
  exact standardNormalAbs_frontier_Iic_null crit

/-- **Hansen Theorem 9.1, asymptotic size bridge for two-sided t tests.**

If the absolute value of a sequence of test statistics `T` converges in
distribution to `|N(0, 1)|`, then the probability of the rejection region
`{|T| > c}` converges to the absolute-standard-normal mass of `(c, ∞)`.

This is the asymptotic-size half of Hansen Theorem 9.1, stated generically over
the test statistic so that the remaining Chapter 9 t-test endpoints can reuse
it. It is the rejection-region counterpart of the Chapter 7 confidence-interval
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
claim to the robust Wald wrapper. Nonlinear efficient-MD criterion tests remain
pending. -/
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
the rejection-probability claim to the homoskedastic Wald wrapper. Nonlinear
homoskedastic MD criterion tests remain pending. -/
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

end HansenEconometrics
