import HansenEconometrics.AsymptoticInterfaces
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.StochasticOrder
import HansenEconometrics.AsymptoticUtils.DeltaMethod
import HansenEconometrics.AsymptoticUtils.MaxBounds
import HansenEconometrics.GaussianLinearization
import HansenEconometrics.Chapter6Asymptotics

/-!
# MetricsLib: asymptotics

Stable import facade for convergence in measure and distribution, stochastic
order, WLLN and CLT wrappers, Delta methods, maximal bounds, stable estimator
interfaces, and Gaussian linearization.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

namespace AsymptoticallyLinearEstimator

variable {Omega k : Type*} [MeasurableSpace Omega] [Fintype k] [DecidableEq k]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- Method-style MetricsLib wrapper for the Gaussian limit of an
asymptotically linear estimator. -/
theorem tendstoInDistribution_multivariateGaussian
    {Y T : Nat -> Omega -> k -> Real} {A S : Matrix k k Real}
    (hlinear : HansenEconometrics.AsymptoticallyLinearEstimator mu Y A T)
    (hT : GaussianLimit mu T S) :
    TendstoInDistribution Y atTop (fun z : EuclideanSpace Real k => z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (A * S * A.transpose)) :=
  asymptoticallyLinearEstimator_tendstoInDistribution_multivariateGaussian_of_gaussianLimit
    Y A S T hlinear hT

end AsymptoticallyLinearEstimator

end HansenEconometrics
