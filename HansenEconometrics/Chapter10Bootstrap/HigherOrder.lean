import HansenEconometrics.Chapter10Bootstrap.PercentileT
import HansenEconometrics.Chapter10Bootstrap.Tests

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section HigherOrderRefinements

/-- Generic second-order probability transfer.

If a fixed-critical probability sequence has a scaled second-order expansion
and another probability sequence differs from it by `o(n⁻¹)`, then the second
sequence has the same scaled expansion.  This is the algebraic transfer used
after a bootstrap critical-value or quantile argument has supplied the
`o(n⁻¹)` replacement error. -/
theorem secondOrder_scaled_probability_transfer
    {fixed random : ℕ → ℝ} {target : ℝ} {bias : ℕ → ℝ}
    (hfixed :
      Tendsto (fun n : ℕ => (n : ℝ) * (fixed n - target + bias n))
        atTop (𝓝 0))
    (hreplacement :
      Tendsto (fun n : ℕ => (n : ℝ) * (random n - fixed n))
        atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (random n - target + bias n))
      atTop (𝓝 0) := by
  have hsum := hfixed.add hreplacement
  have heq :
      (fun n : ℕ => (n : ℝ) * (fixed n - target + bias n) +
        (n : ℝ) * (random n - fixed n)) =
      (fun n : ℕ => (n : ℝ) * (random n - target + bias n)) := by
    funext n
    ring
  simpa [heq] using hsum

/-- Percentile-`t` second-order coverage transfer from a fixed-critical
interval to a random/bootstrap-critical interval. -/
theorem chapter10_percentileT_secondOrder_interval_transfer
    {fixedCoverage randomCoverage : ℕ → ℝ} {coverage K : ℝ}
    (hfixed :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (fixedCoverage n - coverage - (n : ℝ)⁻¹ * K))
        atTop (𝓝 0))
    (hreplacement :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (randomCoverage n - fixedCoverage n))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomCoverage n - coverage - (n : ℝ)⁻¹ * K))
      atTop (𝓝 0) :=
  secondOrder_scaled_probability_transfer
    (fixed := fixedCoverage) (random := randomCoverage)
    (target := coverage) (bias := fun n : ℕ => -((n : ℝ)⁻¹ * K))
    (by simpa [sub_eq_add_neg] using hfixed)
    hreplacement

/-- Two-sided bootstrap-test second-order rejection-probability transfer from
a fixed critical value to a random/bootstrap critical value. -/
theorem chapter10_abs_test_secondOrder_rejection_transfer
    {fixedReject randomReject : ℕ → ℝ} {alpha K : ℝ}
    (hfixed :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (fixedReject n - alpha + (n : ℝ)⁻¹ * K))
        atTop (𝓝 0))
    (hreplacement :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (randomReject n - fixedReject n))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomReject n - alpha + (n : ℝ)⁻¹ * K))
      atTop (𝓝 0) :=
  secondOrder_scaled_probability_transfer
    (fixed := fixedReject) (random := randomReject)
    (target := alpha) (bias := fun n : ℕ => (n : ℝ)⁻¹ * K)
    hfixed hreplacement

/-- Hansen Theorem 10.15, Edgeworth component of the percentile-`t` refinement.

A second-order Edgeworth expansion for a scalar t-ratio gives the symmetric
interval probability expansion used by the percentile-`t` bootstrap interval.
The even `p₁` and odd `p₂` hypotheses encode the cancellation of the
`n^{-1/2}` Edgeworth term in two-sided intervals. -/
theorem chapter10_percentileT_secondOrder_interval_expansion
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c coverage : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            coverage -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) := by
  simpa [hcoverage] using
    h.symmetric_interval_scaled_remainder_tendsto_zero c hp1 hp2 hdensity

/-- Hansen Theorem 10.15 transfer form.

Once the bootstrap percentile-`t` quantile argument supplies an `o(n⁻¹)`
difference between the random interval coverage and the fixed symmetric
interval coverage, the fixed-critical Edgeworth expansion transfers to the
random/bootstrap interval. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c coverage : ℝ} {randomCoverage : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomCoverage n -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomCoverage n -
            coverage -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_transfer
    (fixedCoverage := fun n : ℕ =>
      statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))
    (randomCoverage := randomCoverage)
    (coverage := coverage) (K := 2 * (p2 c * density c))
    (chapter10_percentileT_secondOrder_interval_expansion
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := p1) (p2 := p2) (c := c) (coverage := coverage)
      h hp1 hp2 hdensity hcoverage)
    hreplacement

/-- Hansen Theorem 10.15 transfer form for the actual percentile-`t` interval
event.

The only remaining premise is the theorem's higher-order bootstrap-quantile
replacement step: the event probability of the random percentile-`t` interval
differs from the fixed symmetric interval probability by `o(n⁻¹)`. -/
theorem chapter10_percentileT_secondOrder_interval_event_expansion_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {c coverage : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (((μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
                  (qLower n ω) (qUpper n ω)}).toReal) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
                (qLower n ω) (qUpper n ω)}).toReal) -
            coverage -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := p1) (p2 := p2) (c := c) (coverage := coverage)
    (randomCoverage := fun n : ℕ =>
      (μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
        (qLower n ω) (qUpper n ω)}).toReal)
    h hp1 hp2 hdensity hcoverage hreplacement

/-- Hansen Theorem 10.15, percentile-`t` second-order interval expansion in
the textbook `1 - α` coverage form. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_one_sub_alpha
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            ((1 : ℝ) - alpha) -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_expansion
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := p1) (p2 := p2) (c := c)
    (coverage := (1 : ℝ) - alpha) h hp1 hp2 hdensity hcoverage

/-- Hansen Theorem 10.15 transfer form in the textbook `1 - α` coverage
normalization. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_one_sub_alpha_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c alpha : ℝ} {randomCoverage : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomCoverage n -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomCoverage n -
            ((1 : ℝ) - alpha) -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := p1) (p2 := p2) (c := c)
    (coverage := (1 : ℝ) - alpha) (randomCoverage := randomCoverage)
    h hp1 hp2 hdensity hcoverage hreplacement

/-- Event-probability form of Hansen Theorem 10.15 with limiting coverage
`1 - α`. -/
theorem
chapter10_percentileT_secondOrder_interval_event_expansion_one_sub_alpha_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (((μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
                  (qLower n ω) (qUpper n ω)}).toReal) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
                (qLower n ω) (qUpper n ω)}).toReal) -
            ((1 : ℝ) - alpha) -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_event_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := p1) (p2 := p2) (θ := θ) (θhat := θhat) (se := se)
    (qLower := qLower) (qUpper := qUpper) (c := c)
    (coverage := (1 : ℝ) - alpha)
    h hp1 hp2 hdensity hcoverage hreplacement

/-- Polynomial-shape specialization of
`chapter10_percentileT_secondOrder_interval_expansion`.

This is the theorem-facing Chapter 10 wrapper for Hansen's even-quadratic
`p₁` and odd degree-five `p₂` Edgeworth polynomial shapes. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_polynomial
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c coverage : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            coverage -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) := by
  simpa [hcoverage] using
    h.symmetric_interval_scaled_remainder_tendsto_zero_polynomial (c := c) hdensity

/-- Polynomial-shape specialization of
`chapter10_percentileT_secondOrder_interval_expansion_of_transfer`. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_polynomial_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c coverage : ℝ} {randomCoverage : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomCoverage n -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomCoverage n -
            coverage -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (c := c) (coverage := coverage) (randomCoverage := randomCoverage)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage
    hreplacement

/-- Polynomial-shape percentile-`t` interval event transfer. -/
theorem
chapter10_percentileT_secondOrder_interval_event_expansion_polynomial_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {a0 a2 b1 b3 b5 c coverage : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (((μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
                  (qLower n ω) (qUpper n ω)}).toReal) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
                (qLower n ω) (qUpper n ω)}).toReal) -
            coverage -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_event_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (θ := θ) (θhat := θhat) (se := se)
    (qLower := qLower) (qUpper := qUpper)
    (c := c) (coverage := coverage)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage
    hreplacement

/-- Polynomial-shape specialization of
`chapter10_percentileT_secondOrder_interval_expansion_one_sub_alpha`. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_polynomial_one_sub_alpha
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            ((1 : ℝ) - alpha) -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_expansion_one_sub_alpha
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (c := c) (alpha := alpha)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage

/-- Polynomial-shape specialization of the `1 - α` transfer form for Hansen
Theorem 10.15. -/
theorem
chapter10_percentileT_secondOrder_interval_expansion_polynomial_one_sub_alpha_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ} {randomCoverage : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomCoverage n -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomCoverage n -
            ((1 : ℝ) - alpha) -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_expansion_one_sub_alpha_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (c := c) (alpha := alpha) (randomCoverage := randomCoverage)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage
    hreplacement

/-- Polynomial-shape event-probability form of Hansen Theorem 10.15 with
limiting coverage `1 - α`. -/
theorem
chapter10_percentileT_secondOrder_interval_event_expansion_polynomial_one_sub_alpha_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (((μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
                  (qLower n ω) (qUpper n ω)}).toReal) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
                (qLower n ω) (qUpper n ω)}).toReal) -
            ((1 : ℝ) - alpha) -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_event_expansion_one_sub_alpha_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (θ := θ) (θhat := θhat) (se := se)
    (qLower := qLower) (qUpper := qUpper)
    (c := c) (alpha := alpha)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage
    hreplacement

/-- Hansen Theorem 10.17, fixed-critical Edgeworth component.

For a two-sided test using a fixed critical value `c`, the rejection probability
`1 - (Fₙ(c) - Fₙ(-c))` inherits the symmetric second-order Edgeworth expansion.
The bootstrap-quantile step of Theorem 10.17 supplies the additional
critical-value transfer premise needed to turn this fixed-critical expansion
into the `o(n^{-1})` bootstrap-test refinement. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((1 : ℝ) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))) -
            alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) := by
  have hinterval :=
    h.symmetric_interval_scaled_remainder_tendsto_zero c hp1 hp2 hdensity
  have hneg := hinterval.neg
  have heq :
      (fun n : ℕ =>
        (n : ℝ) *
          (((1 : ℝ) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))) -
            alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c)))) =ᶠ[atTop]
      (fun n : ℕ =>
        -((n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            (baseCDF c - baseCDF (-c)) -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))) := by
    filter_upwards with n
    rw [← halpha]
    ring
  rw [tendsto_congr' heq]
  simpa using hneg

/-- Hansen Theorem 10.17 transfer form.

Once the bootstrap critical-value argument supplies an `o(n⁻¹)` difference
between the random-critical rejection probability and the fixed-critical
rejection probability, the fixed-critical Edgeworth expansion transfers to the
bootstrap test. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c alpha : ℝ} {randomReject : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomReject n -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomReject n - alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_transfer
    (fixedReject := fun n : ℕ =>
      (1 : ℝ) - (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))
    (randomReject := randomReject)
    (alpha := alpha) (K := 2 * (p2 c * density c))
    (chapter10_abs_test_secondOrder_rejection_expansion
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := p1) (p2 := p2) (c := c) (alpha := alpha)
      h hp1 hp2 hdensity halpha)
    hreplacement

/-- Hansen Theorem 10.17 transfer form for the actual two-sided bootstrap-test
event.

The replacement premise is the theorem's higher-order bootstrap critical-value
step: replacing the fixed critical value `c` by the random/bootstrap critical
value changes the rejection probability by `o(n⁻¹)`. -/
theorem chapter10_abs_test_secondOrder_rejection_event_expansion_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {crit : ℕ → Ω → ℝ} {c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (((μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal) -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal) -
            alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := p1) (p2 := p2) (c := c) (alpha := alpha)
    (randomReject := fun n : ℕ =>
      (μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal)
    h hp1 hp2 hdensity halpha hreplacement

/-- Hansen Theorem 10.17 in the textbook central-coverage calibration form.

The fixed critical value is calibrated by `F(c) - F(-c) = 1 - α`, so the
two-sided rejection probability has limiting size `α` with the same
second-order correction as `chapter10_abs_test_secondOrder_rejection_expansion`. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_one_sub_alpha
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((1 : ℝ) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))) -
            alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) := by
  have halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha := by
    rw [hcoverage]
    ring
  exact
    chapter10_abs_test_secondOrder_rejection_expansion
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := p1) (p2 := p2) (c := c) (alpha := alpha)
      h hp1 hp2 hdensity halpha

/-- Hansen Theorem 10.17 transfer form with textbook central coverage
`F(c) - F(-c) = 1 - α`. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_one_sub_alpha_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c alpha : ℝ} {randomReject : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomReject n -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomReject n - alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) := by
  have halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha := by
    rw [hcoverage]
    ring
  exact
    chapter10_abs_test_secondOrder_rejection_expansion_of_transfer
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := p1) (p2 := p2) (c := c) (alpha := alpha)
      (randomReject := randomReject)
      h hp1 hp2 hdensity halpha hreplacement

/-- Event-probability form of Hansen Theorem 10.17 with central coverage
`F(c) - F(-c) = 1 - α`. -/
theorem
chapter10_abs_test_secondOrder_rejection_event_expansion_one_sub_alpha_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {crit : ℕ → Ω → ℝ} {c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (((μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal) -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal) -
            alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) := by
  have halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha := by
    rw [hcoverage]
    ring
  exact
    chapter10_abs_test_secondOrder_rejection_event_expansion_of_transfer
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := p1) (p2 := p2) (crit := crit) (c := c) (alpha := alpha)
      h hp1 hp2 hdensity halpha hreplacement

/-- Polynomial-shape specialization of
`chapter10_abs_test_secondOrder_rejection_expansion`. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_polynomial
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((1 : ℝ) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))) -
            alpha +
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) := by
  exact
    chapter10_abs_test_secondOrder_rejection_expansion
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := edgeworthP1Polynomial a0 a2)
      (p2 := edgeworthP2Polynomial b1 b3 b5)
      (c := c) (alpha := alpha) h
      (edgeworthP1Polynomial_neg a0 a2 c)
      (edgeworthP2Polynomial_neg b1 b3 b5 c)
      hdensity halpha

/-- Polynomial-shape specialization of
`chapter10_abs_test_secondOrder_rejection_expansion_of_transfer`. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_polynomial_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ} {randomReject : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomReject n -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomReject n - alpha +
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (c := c) (alpha := alpha) (randomReject := randomReject)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity halpha
    hreplacement

/-- Polynomial-shape two-sided bootstrap-test event transfer. -/
theorem
chapter10_abs_test_secondOrder_rejection_event_expansion_polynomial_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {crit : ℕ → Ω → ℝ} {a0 a2 b1 b3 b5 c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (((μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal) -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal) -
            alpha +
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_event_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (crit := crit) (c := c) (alpha := alpha)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity halpha
    hreplacement

/-- Polynomial-shape specialization of
`chapter10_abs_test_secondOrder_rejection_expansion_one_sub_alpha`. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_polynomial_one_sub_alpha
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((1 : ℝ) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))) -
            alpha +
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_expansion_one_sub_alpha
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (c := c) (alpha := alpha)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage

/-- Polynomial-shape specialization of the `1 - α` transfer form for Hansen
Theorem 10.17. -/
theorem
chapter10_abs_test_secondOrder_rejection_expansion_polynomial_one_sub_alpha_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ} {randomReject : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomReject n -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomReject n - alpha +
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_expansion_one_sub_alpha_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (c := c) (alpha := alpha) (randomReject := randomReject)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage
    hreplacement

/-- Polynomial-shape event-probability form of Hansen Theorem 10.17 with
central coverage `1 - α`. -/
theorem
chapter10_abs_test_secondOrder_rejection_event_expansion_polynomial_one_sub_alpha_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {crit : ℕ → Ω → ℝ} {a0 a2 b1 b3 b5 c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = (1 : ℝ) - alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (((μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal) -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)}).toReal) -
            alpha +
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_event_expansion_one_sub_alpha_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (crit := crit) (c := c) (alpha := alpha)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage
    hreplacement

end HigherOrderRefinements

end HansenEconometrics
