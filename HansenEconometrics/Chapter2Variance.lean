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

/-- Hansen Theorem 2.5: if `Y` has a finite second moment (`MemLp Y 2 μ`),
then the CEF error `e = Y - E[Y|m]` also has a finite second moment,
i.e., the regression-error variance σ² < ∞. -/
theorem memLp_cefError
    {Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) :
    MemLp (cefError μ Y m) 2 μ :=
  hY.sub hY.condExp

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

/-- Hansen Theorem 2.6:
monotonic decrease of residual variance under larger conditioning sets.
If `m₁ ≤ m₂ ≤ m₀`, then `Var[Y - E[Y|m₂]] ≤ Var[Y - E[Y|m₁]]`,
i.e., conditioning on more information (weakly) reduces
the variance of the regression error. -/
theorem variance_cefError_antitone
    {m₁ m₂ : MeasurableSpace Ω}
    {Y : Ω → ℝ}
    (hm₁₂ : m₁ ≤ m₂)
    (hm₂₀ : m₂ ≤ m₀)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    Var[cefError μ Y m₂; μ] ≤ Var[cefError μ Y m₁; μ] := by
  have hm₁₀ : m₁ ≤ m₀ := le_trans hm₁₂ hm₂₀
  have hYi : Integrable Y μ := hY.integrable one_le_two
  -- Conditional expectation MemLp facts
  have hce₁ : MemLp (μ[Y | m₁]) 2 μ := hY.condExp
  have hce₂ : MemLp (μ[Y | m₂]) 2 μ := hY.condExp
  -- Step 1: Var[cefError μ Y m] = μ[Var[Y|m]] since E[cefError] = 0
  have hv₁ : Var[cefError μ Y m₁; μ] = ∫ ω, Var[Y; μ | m₁] ω ∂μ := by
    rw [variance_of_integral_eq_zero (memLp_cefError (m := m₁) hY).aemeasurable
      (integral_cefError_zero (m := m₁) (m₀ := m₀) hm₁₀ hYi)]
    exact (integral_condVar_eq_integral_cefError_sq (m := m₁) (m₀ := m₀) hm₁₀
      (hY.sub hce₁).integrable_sq).symm
  have hv₂ : Var[cefError μ Y m₂; μ] = ∫ ω, Var[Y; μ | m₂] ω ∂μ := by
    rw [variance_of_integral_eq_zero (memLp_cefError (m := m₂) hY).aemeasurable
      (integral_cefError_zero (m := m₂) (m₀ := m₀) hm₂₀ hYi)]
    exact (integral_condVar_eq_integral_cefError_sq (m := m₂) (m₀ := m₀) hm₂₀
      (hY.sub hce₂).integrable_sq).symm
  rw [hv₂, hv₁]
  -- Goal: μ[Var[Y|m₂]] ≤ μ[Var[Y|m₁]]
  -- Step 2: From variance decomposition, μ[Var[Y|m]] = Var[Y] - Var[μ[Y|m]]
  have hd₁ := variance_decomposition (m := m₁) (m₀ := m₀) hm₁₀ hY
  have hd₂ := variance_decomposition (m := m₂) (m₀ := m₀) hm₂₀ hY
  -- Step 3: Explained variance is monotone: Var[μ[Y|m₁]] ≤ Var[μ[Y|m₂]]
  -- By the tower property and variance_condExp_le_variance
  have htower := tower_property (Ω := Ω) (μ := μ) (Y := Y)
    (m₁ := m₁) (m₂ := m₂) (m₀ := m₀) hm₁₂ hm₂₀
  have hmono : Var[μ[Y | m₁]; μ] ≤ Var[μ[Y | m₂]; μ] :=
    calc Var[μ[Y | m₁]; μ]
        = Var[μ[μ[Y | m₂] | m₁]; μ] := (variance_congr htower).symm
      _ ≤ Var[μ[Y | m₂]; μ] :=
          variance_condExp_le_variance (m := m₁) (m₀ := m₀) hm₁₀ hce₂
  linarith

section ProbabilityOnRandomVars

variable {β γ : Type*}
variable [MeasurableSpace β] [MeasurableSpace γ]

/-- Law of total variance stated in terms of a conditioning variable `X`. -/
theorem law_total_variance_rv
    {Y : Ω → ℝ} {X : Ω → β}
    (hX : Measurable X)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    μ[condVarOn μ Y X] + Var[condExpOn μ Y X; μ] = Var[Y; μ] := by
  simpa [condVarOn, condExpOn, conditioningSpace] using
    law_total_variance
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      (conditioningSpace_le hX)
      hY

/-- The explained variance from conditioning on `X` is bounded by the total variance. -/
theorem variance_condExpOn_le_variance
    {Y : Ω → ℝ} {X : Ω → β}
    (hX : Measurable X)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    Var[condExpOn μ Y X; μ] ≤ Var[Y; μ] := by
  simpa [condExpOn, conditioningSpace] using
    variance_condExp_le_variance
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      (conditioningSpace_le hX)
      hY

/-- Richer conditioning variables weakly reduce the residual variance. -/
theorem residualVarOn_antitone
    {Y : Ω → ℝ} {X₁ : Ω → β} {X₂ : Ω → γ}
    (hX : conditioningSpace X₁ ≤ conditioningSpace X₂)
    (hX₂ : Measurable X₂)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    residualVarOn μ Y X₂ ≤ residualVarOn μ Y X₁ := by
  simpa [residualVarOn, conditioningSpace] using
    variance_cefError_antitone
      (m₁ := conditioningSpace X₁)
      (m₂ := conditioningSpace X₂)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      hX
      (conditioningSpace_le hX₂)
      hY

/-- If `X₁ = f(X₂)` for a measurable `f`, then conditioning on `X₂` weakly reduces residual
variance relative to conditioning on `X₁`. -/
theorem residualVarOn_antitone_of_factor
    {Y : Ω → ℝ} {X₁ : Ω → β} {X₂ : Ω → γ} {f : γ → β}
    (hf : Measurable f)
    (hX₂ : Measurable X₂)
    (hX : X₁ = f ∘ X₂)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    residualVarOn μ Y X₂ ≤ residualVarOn μ Y X₁ :=
  residualVarOn_antitone
    (μ := μ)
    (Y := Y)
    (conditioningSpace_le_of_factor (hf := hf) hX)
    hX₂
    hY

end ProbabilityOnRandomVars

end HansenEconometrics
