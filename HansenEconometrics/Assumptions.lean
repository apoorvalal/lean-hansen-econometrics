import HansenEconometrics.Assumptions.Conditioning
import HansenEconometrics.Assumptions.Regression
import HansenEconometrics.Assumptions.Chapter4OLS
import HansenEconometrics.Assumptions.Chapter7Iid

/-!
# Textbook-Facing Assumption Setups

This umbrella module exposes the compact setup structures used to package
recurring probability, regression, OLS, and Chapter 7 iid assumptions.

The structures in this namespace are public-facing assumption surfaces. Their
methods convert to the older sigma-algebra, finite-sample, and asymptotic
proof engines when those engines are still the shortest way to prove the
textbook theorem.
-/
