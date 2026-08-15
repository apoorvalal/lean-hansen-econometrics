import HansenEconometrics.MetricsLib.LinearAlgebra
import HansenEconometrics.MetricsLib.Probability
import HansenEconometrics.MetricsLib.Asymptotics
import HansenEconometrics.MetricsLib.Regression
import HansenEconometrics.MetricsLib.Inference
import HansenEconometrics.MetricsLib.Bootstrap

/-!
# MetricsLib

`HansenEconometrics.MetricsLib` is the curated reusable surface of the Hansen
formalization. It packages the workhorse linear algebra, probability,
asymptotic, regression, inference, and bootstrap APIs behind stable import
paths.

Use this root import when developing a new econometric result. Use one of the
domain modules under `HansenEconometrics.MetricsLib` when a smaller dependency
surface is preferable. Chapter modules remain the source for textbook-facing
wrappers and specialized IV, multivariate-regression, and GMM developments.
-/
