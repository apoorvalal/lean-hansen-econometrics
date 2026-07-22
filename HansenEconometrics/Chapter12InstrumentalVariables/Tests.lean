import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import HansenEconometrics.Chapter5LikelihoodRatioTest
import HansenEconometrics.Chapter9HypothesisTesting
import HansenEconometrics.FDist

/-!
# Chapter 12 - IV tests

This module records the Wald, endogeneity, overidentification, and subset
overidentification test surfaces from Hansen's instrumental-variables chapter.
The distributional lemmas below are interface projections. The substantive
finite-sample `N = C*` definitions and proof for Hansen Theorem 12.17 live in
`Chapter12InstrumentalVariables.Overidentification`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory ENNReal

namespace HansenEconometrics

open Matrix

variable {Omega k q r : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable [Fintype k] [Fintype q] [Fintype r]
variable [DecidableEq k] [DecidableEq q] [DecidableEq r]

/-- Generic IV Wald statistic for a restriction vector. -/
noncomputable def ivWaldStatistic (theta : q → ℝ) (Vtheta : Matrix q q ℝ) : ℝ :=
  theta ⬝ᵥ (Vtheta⁻¹ *ᵥ theta)

/-- Endogeneity-test statistic comparing OLS and IV estimators. -/
noncomputable def hausmanEndogeneityStatistic
    (delta : k → ℝ) (Vdelta : Matrix k k ℝ) : ℝ :=
  ivWaldStatistic delta Vdelta

/-- Sargan/Hansen overidentification statistic. -/
noncomputable def overidentificationStatistic
    (gbar : q → ℝ) (What : Matrix q q ℝ) : ℝ :=
  gbar ⬝ᵥ (What *ᵥ gbar)

/-- Subset overidentification statistic. -/
noncomputable def subsetOveridentificationStatistic
    (gbar : q → ℝ) (C : Matrix q r ℝ) (What : Matrix q q ℝ) : ℝ :=
  ivWaldStatistic (Cᵀ *ᵥ gbar) (Cᵀ * What * C)

/-- Interface projection for an IV Wald statistic with a chi-square null limit. -/
theorem ivWald_chiSquaredLimit_from_interface
    (W : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) :=
  hW

/-- **Hansen Theorem 12.6, test-size layer.**

Once the 2SLS nonlinear Wald statistic has the chi-square null limit and the
critical value is calibrated to the chi-square upper tail, the rejection
probability has asymptotic size `alpha`. The Gaussian and covariance-consistency
inputs are supplied by the Chapter 12.5 route; this theorem reuses Chapter 9's
generic chi-square rejection-probability bridge. -/
theorem chapter12_theorem_12_6_ivWald_rejectionProb_tendsto_alpha
    (W : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {ω | crit < W n ω}) atTop (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := mu) (W := W) (q := df) (crit := crit) hcrit hW

/-- Interface projection for the robust control-function endogeneity Wald limit. -/
theorem endogeneityWald_chiSquaredLimit_from_interface
    (W : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) :=
  hW

/-- **Hansen Theorem 12.14, size conclusion.**

Given the control-function endogeneity Wald statistic's `χ²(k₂)` limit under
`H₀ : α = 0`, the upper-tail test has asymptotic size `alpha`. This is the
Chapter 12 specialization of the reusable Chapter 9 chi-square test-size
theorem. -/
theorem chapter12_theorem_12_14_endogeneityWald_rejectionProb_tendsto_alpha
    (W : ℕ → Omega → ℝ) (k2 : ℕ) [Fact (0 < k2)]
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared k2) (Set.Ioi crit) = alpha)
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared k2)) :
    Tendsto (fun n => mu {ω | crit < W n ω}) atTop (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := mu) (W := W) (q := k2) (crit := crit) hcrit hW

omit [IsProbabilityMeasure mu] in
/-- Interface projection for the finite-sample endogeneity F law. -/
theorem endogeneityF_hasLaw_from_interface
    (Fstat : Omega → ℝ) (df1 df2 : ℕ)
    (hF : HasLaw Fstat (classicalFDist df1 df2) mu) :
    HasLaw Fstat (classicalFDist df1 df2) mu :=
  hF

omit [Fintype k] [Fintype q] [Fintype r] [DecidableEq k] [DecidableEq q] [DecidableEq r]
    [IsProbabilityMeasure mu] in
/-- **Hansen Theorem 12.15, exact finite-sample F law.**

The control-function endogeneity F statistic is an ordinary fixed-design block
OLS F statistic once the generated residual is included in the design and the
null coefficient block is zero. This wrapper reuses the Chapter 5 exact block-F
law, with `X₁` representing the maintained regressors and `X₂` the tested
control-function residual block. -/
theorem chapter12_theorem_12_15_endogeneityF_hasLaw_classicalFDist
    {n k1 k2 : Type*} [Fintype n] [Fintype k1] [Fintype k2]
    [DecidableEq n] [DecidableEq k1] [DecidableEq k2]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k1 ℝ) (X₂ : Matrix n k2 ℝ) (β₁ : k1 → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k2)
    (hdf : Fintype.card (Sum k1 k2) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)))
      (classicalFDist (Fintype.card k2)
        (Fintype.card n - Fintype.card (Sum k1 k2))) μ :=
  olsFStatistic_hasLaw_classicalFDist X₁ X₂ β₁ hσ2 hq hdf ε hε

omit [Fintype k] [Fintype q] [Fintype r] [DecidableEq k] [DecidableEq q] [DecidableEq r]
    [IsProbabilityMeasure mu] in
/-- **Hansen Theorem 12.15, exact size conclusion.**

If the F critical value is calibrated to the `F(k₂, n-k)` upper tail, the
control-function endogeneity F test has exact finite-sample size `alpha`. -/
theorem chapter12_theorem_12_15_endogeneityF_rejection_probability_eq_alpha
    {n k1 k2 : Type*} [Fintype n] [Fintype k1] [Fintype k2]
    [DecidableEq n] [DecidableEq k1] [DecidableEq k2]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k1 ℝ) (X₂ : Matrix n k2 ℝ) (β₁ : k1 → ℝ)
    {σ2 alpha : ℝ} (crit : ℝ)
    (hcrit :
      (classicalFDist (Fintype.card k2)
        (Fintype.card n - Fintype.card (Sum k1 k2))).real (Set.Ioi crit) = alpha)
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k2)
    (hdf : Fintype.card (Sum k1 k2) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | crit < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} = alpha :=
  olsFStatistic_rejection_probability_eq_alpha_classical
    X₁ X₂ β₁ crit hcrit hσ2 hq hdf ε hε

/-- Interface projection for the overidentification statistic's chi-square null limit. -/
theorem overidentification_chiSquaredLimit_from_interface
    (J : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    (hJ : TendstoInDistribution J atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    TendstoInDistribution J atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) :=
  hJ

/-- **Hansen Theorem 12.16, size conclusion.**

Given the Sargan statistic's `χ²(ℓ-k)` limit, the upper-tail Sargan test has
asymptotic size `alpha`. The difficult Chapter 12 work is proving the Sargan
chi-square limit from Assumption 12.2 plus conditional homoskedasticity; this
wrapper reuses the generic Chapter 9 probability bridge for the size step. -/
theorem chapter12_theorem_12_16_sargan_rejectionProb_tendsto_alpha
    (S : ℕ → Omega → ℝ) (overidDf : ℕ) [Fact (0 < overidDf)]
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared overidDf) (Set.Ioi crit) = alpha)
    (hS : TendstoInDistribution S atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared overidDf)) :
    Tendsto (fun n => mu {ω | crit < S n ω}) atTop (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := mu) (W := S) (q := overidDf) (crit := crit) hcrit hS

/-- Interface projection for the subset-overidentification statistic's chi-square
null limit. -/
theorem subsetOveridentification_chiSquaredLimit_from_interface
    (Nstat : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    (hN : TendstoInDistribution Nstat atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    TendstoInDistribution Nstat atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) :=
  hN

/-- **Hansen Theorem 12.17, distributional test-size layer.**

After the algebraic identity `N = C*` and the asymptotic equivalence of the
convenient difference statistic `C` to `C*` have supplied chi-square limits for
both statistics, both upper-tail subset-overidentification tests have
asymptotic size `alpha`. -/
theorem chapter12_theorem_12_17_subsetOveridentification_rejectionProbs_tendsto_alpha
    (Nstat Cstat : ℕ → Omega → ℝ) (lb : ℕ) [Fact (0 < lb)]
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared lb) (Set.Ioi crit) = alpha)
    (hN : TendstoInDistribution Nstat atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared lb))
    (hC : TendstoInDistribution Cstat atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared lb)) :
    Tendsto (fun n => mu {ω | crit < Nstat n ω}) atTop (𝓝 alpha) ∧
      Tendsto (fun n => mu {ω | crit < Cstat n ω}) atTop (𝓝 alpha) :=
  ⟨chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
      (μ := mu) (W := Nstat) (q := lb) (crit := crit) hcrit hN,
    chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
      (μ := mu) (W := Cstat) (q := lb) (crit := crit) hcrit hC⟩

end HansenEconometrics
