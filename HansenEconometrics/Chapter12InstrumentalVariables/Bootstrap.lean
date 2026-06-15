import HansenEconometrics.Chapter10Bootstrap.WeakDistribution

/-!
# Chapter 12 - bootstrap for 2SLS

This module connects the bootstrap 2SLS route to the reusable Chapter 10
conditional weak-convergence interface. The bridge below is not a proof of
Hansen Theorem 12.8 from Assumption 12.2.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Omega OmegaS OmegaLim E : Type*}
variable [MeasurableSpace Omega] [MeasurableSpace OmegaS] [MeasurableSpace OmegaLim]
variable [TopologicalSpace E]
variable {mu : Measure Omega}

/-- Interface projection for bootstrap consistency of a 2SLS statistic. -/
theorem twoStageLeastSquares_bootstrap_from_interface
    (Pstar : ℕ → Omega → Measure OmegaS)
    (Tstar : ℕ → Omega → OmegaS → E)
    (nu : Measure OmegaLim) (Tlim : OmegaLim → E)
    (hT : TendstoInBootstrapWeakDistribution mu Pstar Tstar nu Tlim) :
    TendstoInBootstrapWeakDistribution mu Pstar Tstar nu Tlim :=
  hT

end HansenEconometrics
