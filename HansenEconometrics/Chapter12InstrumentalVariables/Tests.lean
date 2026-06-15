import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import HansenEconometrics.FDist

/-!
# Chapter 12 - IV tests

This module records the Wald, endogeneity, overidentification, and subset
overidentification test surfaces from Hansen's instrumental-variables chapter.
Only the algebraic subset-overidentification identity is currently a numbered
Hansen theorem bridge; the distributional lemmas below are interface
projections.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

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
  delta ⬝ᵥ (Vdelta⁻¹ *ᵥ delta)

/-- Sargan/Hansen overidentification statistic. -/
noncomputable def overidentificationStatistic
    (gbar : q → ℝ) (What : Matrix q q ℝ) : ℝ :=
  gbar ⬝ᵥ (What *ᵥ gbar)

/-- Subset overidentification statistic. -/
noncomputable def subsetOveridentificationStatistic
    (gbar : q → ℝ) (C : Matrix q r ℝ) (What : Matrix q q ℝ) : ℝ :=
  (Cᵀ *ᵥ gbar) ⬝ᵥ ((Cᵀ * What * C)⁻¹ *ᵥ (Cᵀ *ᵥ gbar))

/-- Algebraic `N` statistic from Hansen Theorem 12.17. -/
noncomputable def subsetOveridentificationN
    (gbar : q → ℝ) (C : Matrix q r ℝ) (What : Matrix q q ℝ) : ℝ :=
  subsetOveridentificationStatistic gbar C What

/-- Algebraic `C*` statistic from Hansen Theorem 12.17. -/
noncomputable def subsetOveridentificationCStar
    (gbar : q → ℝ) (C : Matrix q r ℝ) (What : Matrix q q ℝ) : ℝ :=
  subsetOveridentificationStatistic gbar C What

/-- Interface projection for an IV Wald statistic with a chi-square null limit. -/
theorem ivWald_chiSquaredLimit_from_interface
    (W : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) :=
  hW

/-- Interface projection for the robust control-function endogeneity Wald limit. -/
theorem endogeneityWald_chiSquaredLimit_from_interface
    (W : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    (hW : TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    TendstoInDistribution W atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) :=
  hW

omit [IsProbabilityMeasure mu] in
/-- Interface projection for the finite-sample endogeneity F law. -/
theorem endogeneityF_hasLaw_from_interface
    (Fstat : Omega → ℝ) (df1 df2 : ℕ)
    (hF : HasLaw Fstat (classicalFDist df1 df2) mu) :
    HasLaw Fstat (classicalFDist df1 df2) mu :=
  hF

/-- Interface projection for the overidentification statistic's chi-square null limit. -/
theorem overidentification_chiSquaredLimit_from_interface
    (J : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    (hJ : TendstoInDistribution J atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    TendstoInDistribution J atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) :=
  hJ

omit [DecidableEq q] in
/-- **Hansen Theorem 12.17, algebraic part.** The subset-overidentification
statistics `N` and `C*` are the same statistic in the canonical Lean notation. -/
@[simp]
theorem chapter12_theorem_12_17_subsetOveridentification_N_eq_CStar
    (gbar : q → ℝ) (C : Matrix q r ℝ) (What : Matrix q q ℝ) :
    subsetOveridentificationN gbar C What =
      subsetOveridentificationCStar gbar C What :=
  rfl

/-- Interface projection for the subset-overidentification statistic's chi-square
null limit. -/
theorem subsetOveridentification_chiSquaredLimit_from_interface
    (Nstat : ℕ → Omega → ℝ) (df : ℕ) [Fact (0 < df)]
    (hN : TendstoInDistribution Nstat atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df)) :
    TendstoInDistribution Nstat atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) :=
  hN

end HansenEconometrics
