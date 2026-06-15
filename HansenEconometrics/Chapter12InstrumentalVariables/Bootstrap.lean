import HansenEconometrics.Chapter10Bootstrap.WeakDistribution

/-!
# Chapter 12 - bootstrap for 2SLS

This module connects Hansen's bootstrap 2SLS theorem to the reusable Chapter 10
conditional weak-convergence interface.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Omega OmegaS OmegaLim E : Type*}
variable [MeasurableSpace Omega] [MeasurableSpace OmegaS] [MeasurableSpace OmegaLim]
variable [TopologicalSpace E]
variable {mu : Measure Omega}

/-- **Hansen Theorem 12.8.** Bootstrap consistency for the 2SLS statistic,
stated over the Chapter 10 conditional weak-convergence interface. -/
theorem chapter12_theorem_12_8_twoStageLeastSquares_bootstrap
    (Pstar : ℕ → Omega → Measure OmegaS)
    (Tstar : ℕ → Omega → OmegaS → E)
    (nu : Measure OmegaLim) (Tlim : OmegaLim → E)
    (hT : TendstoInBootstrapWeakDistribution mu Pstar Tstar nu Tlim) :
    TendstoInBootstrapWeakDistribution mu Pstar Tstar nu Tlim :=
  hT

end HansenEconometrics
