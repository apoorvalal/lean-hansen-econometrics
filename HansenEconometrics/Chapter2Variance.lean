import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter2CondExp

open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω : Type*}
variable {m m₀ : MeasurableSpace Ω}
variable {μ : Measure Ω}

/-- Hansen Chapter 2.12: the expected conditional variance equals the expected squared
CEF error. This is the regression-error variance identity following Definitions 2.1-2.2. -/
theorem integral_condVar_eq_integral_cefError_sq
    {Y : Ω → ℝ}
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hY2 : Integrable ((Y - μ[Y | m]) ^ 2) μ) :
    ∫ ω, Var[Y; μ | m] ω ∂μ = ∫ ω, (cefError μ Y m ω) ^ 2 ∂μ := by
  simpa [cefError] using
    (ProbabilityTheory.setIntegral_condVar (m := m) (m₀ := m₀) (μ := μ)
      (X := Y) hY2 MeasurableSet.univ)

/-- Hansen Theorem 2.8 / law of total variance in Mathlib form. -/
theorem law_total_variance
    {Y : Ω → ℝ}
    (hm : m ≤ m₀)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    μ[Var[Y; μ | m]] + Var[μ[Y | m]; μ] = Var[Y; μ] := by
  simpa using ProbabilityTheory.integral_condVar_add_variance_condExp (m := m) (m₀ := m₀) (μ := μ)
    (X := Y) hm hY

/-- Hansen Theorem 2.8, rearranged. -/
theorem variance_decomposition
    {Y : Ω → ℝ}
    (hm : m ≤ m₀)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    Var[Y; μ] = μ[Var[Y; μ | m]] + Var[μ[Y | m]; μ] := by
  rw [eq_comm]
  simpa using law_total_variance (m := m) (m₀ := m₀) (μ := μ) (Y := Y) hm hY

/-- The explained variance is bounded by total variance, as a direct consequence of Theorem 2.8. -/
theorem variance_condExp_le_variance
    {Y : Ω → ℝ}
    (hm : m ≤ m₀)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    Var[μ[Y | m]; μ] ≤ Var[Y; μ] := by
  have htv := law_total_variance (m := m) (m₀ := m₀) (μ := μ) (Y := Y) hm hY
  have hY2 : Integrable ((Y - μ[Y | m]) ^ 2) μ := by
    exact (hY.sub hY.condExp).integrable_sq
  have hnonneg : 0 ≤ μ[Var[Y; μ | m]] := by
    rw [integral_condVar_eq_integral_cefError_sq (m := m) (m₀ := m₀) (μ := μ) (Y := Y) hm hY2]
    refine integral_nonneg ?_
    intro ω
    exact sq_nonneg _
  linarith

end HansenEconometrics
