import HansenEconometrics.Chapter7Asymptotics.Inference

/-!
# Chapter 9 — Hypothesis Testing

This file formalizes the asymptotic theory of hypothesis tests from Hansen's
Chapter 9. The current public surface covers the asymptotic-size half of
**Theorem 9.1** (t tests):

* `tTest_rejectionProb_tendsto_of_abs_tstat` — the generic Chapter 9 size
  bridge. If the absolute value of a sequence of test statistics converges in
  distribution to `|N(0, 1)|`, then the rejection probability of the two-sided
  test "reject if `|T| > c`" converges to the absolute-standard-normal mass of
  `(c, ∞)`. This is the asymptotic-size half of Theorem 9.1, stated generically
  so that every Chapter 9 t-test endpoint can reuse it. It is the
  rejection-region counterpart of the Chapter 7 confidence-interval coverage
  bridge `symmetricCI_coverage_of_abs_tstat`.
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

/-- **Hansen Theorem 9.1, asymptotic-size half, for the ordinary-OLS HC0 t-test.**

The two-sided HC0 t-test "reject if `|T| > c`" has asymptotic rejection
probability equal to the absolute-standard-normal mass of `(c, ∞)` — that is,
`P[|Z| > c] = 2(1 - Φ(c))` for `Z ∼ N(0, 1)`.

Scope and faithfulness notes:
* This formalizes only claim (b) of Hansen Theorem 9.1 (the rejection-probability
  limit). Claim (a), `T(θ₀) →d N(0, 1)`, is Hansen Theorem 7.11 and is reused
  via `olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal`. Claim (c),
  "the test has asymptotic size `α`", follows by choosing `c` with
  `2(1 - Φ(c)) = α`, but is not separately stated.
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

end HansenEconometrics
