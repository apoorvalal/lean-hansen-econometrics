import HansenEconometrics.MetricsLib

/-!
# MetricsLib consumer smoke test

This file is compiled outside the library target. It checks that a downstream
project can import the curated facade, find representative workhorse results,
and compose the stable asymptotic interfaces without importing a textbook
chapter directly.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Topology MeasureTheory ProbabilityTheory

#check HansenEconometrics.condExpOn
#check HansenEconometrics.olsBetaStar
#check HansenEconometrics.GramConsistency
#check HansenEconometrics.ScoreCLT
#check HansenEconometrics.CovarianceEstimatorConsistent
#check HansenEconometrics.AsymptoticallyLinearEstimator
#check HansenEconometrics.AsymptoticallyLinearEstimator.tendstoInDistribution_multivariateGaussian
#check HansenEconometrics.covarianceStdErrorScale
#check HansenEconometrics.asymptoticallyLinearEstimator_tendstoInDistribution_multivariateGaussian_of_gaussianLimit
#check HansenEconometrics.TendstoInBootstrapProbability
#check HansenEconometrics.ScoreCLT.ofConditions
#check HansenEconometrics.LeastSquaresConsistencyConditions.toGramConsistency

namespace MetricsLibSmoke

variable {Omega k : Type*} [MeasurableSpace Omega] [Fintype k] [DecidableEq k]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]

/-- A downstream theorem can use the neutral interfaces and workhorse Gaussian
linearization theorem without depending on the chapter that first needed it. -/
example (Y T : Nat -> Omega -> k -> Real) (A S : Matrix k k Real)
    (hlinear : HansenEconometrics.AsymptoticallyLinearEstimator mu Y A T)
    (hT : HansenEconometrics.GaussianLimit mu T S) :
    TendstoInDistribution Y atTop (fun z : EuclideanSpace Real k => z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (A * S * A.transpose)) :=
  hlinear.tendstoInDistribution_multivariateGaussian hT

end MetricsLibSmoke
