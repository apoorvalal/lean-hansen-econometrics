import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Sum of squares of a finite family of real-valued random variables. This is the basic random
variable behind chi-square style constructions. -/
def sumSquaresRV [Fintype ι] (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, (X i ω) ^ 2

lemma sumSquaresRV_nonneg [Fintype ι] (X : ι → Ω → ℝ) (ω : Ω) :
    0 ≤ sumSquaresRV X ω := by
  unfold sumSquaresRV
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Convenient wrapper around Mathlib's jointly-Gaussian + zero-covariance independence lemma for
real-valued pairs. -/
lemma indep_of_jointGaussian_cov_zero
    {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hcov : cov[X, Y; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_eq_zero hcov

/-- Finite-family version of Gaussian independence from pairwise zero covariance. -/
lemma iIndep_of_jointGaussian_cov_zero [Finite ι]
    {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω i => X i ω) P)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_eq_zero hcov

end HansenEconometrics
