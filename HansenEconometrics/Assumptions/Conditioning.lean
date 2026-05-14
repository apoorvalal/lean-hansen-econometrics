import HansenEconometrics.Chapter2Variance

/-!
# Conditional-Expectation Setup Assumptions

This module is the textbook-facing API for recurring Chapter 2 conditioning
hypotheses. The structures package assumptions; theorem methods expose
consequences by delegating to the sigma-algebra backend in `Chapter2CondExp`
and `Chapter2Variance`.
-/

open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω β γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
variable {μ : Measure Ω}

/-- L1 setup for conditional expectation given a random variable. -/
structure ConditionalL1Setup (μ : Measure Ω) (Y : Ω → ℝ) (X : Ω → β) where
  isProbability : IsProbabilityMeasure μ
  measurable_conditioning : Measurable X
  sigmaFinite_trim : SigmaFinite (μ.trim (conditioningSpace_le measurable_conditioning))
  integrable_response : Integrable Y μ

/-- L2 setup for conditional expectation and variance facts given a random variable. -/
structure ConditionalL2Setup (μ : Measure Ω) (Y : Ω → ℝ) (X : Ω → β) where
  isProbability : IsProbabilityMeasure μ
  measurable_conditioning : Measurable X
  sigmaFinite_trim : SigmaFinite (μ.trim (conditioningSpace_le measurable_conditioning))
  memLp_response : MemLp Y 2 μ

/-- L1 predictor measurable with respect to a conditioning variable. -/
structure XPredictorL1 (μ : Measure Ω) (X : Ω → β) (g : Ω → ℝ) where
  x_measurable : XMeasurable μ X g
  integrable_predictor : Integrable g μ

/-- L2 predictor measurable with respect to a conditioning variable. -/
structure XPredictorL2 (μ : Measure Ω) (X : Ω → β) (g : Ω → ℝ) where
  x_measurable : XMeasurable μ X g
  memLp_predictor : MemLp g 2 μ

/-- L1 setup for nested conditioning variables `σ(X₁) ≤ σ(X₂)`. -/
structure NestedConditioningL1Setup
    (μ : Measure Ω) (Y : Ω → ℝ) (X₁ : Ω → β) (X₂ : Ω → γ) where
  isProbability : IsProbabilityMeasure μ
  measurable_finer : Measurable X₂
  sigmaFinite_trim : SigmaFinite (μ.trim (conditioningSpace_le measurable_finer))
  integrable_response : Integrable Y μ
  nested : conditioningSpace X₁ ≤ conditioningSpace X₂

/-- L2 setup for nested conditioning variables `σ(X₁) ≤ σ(X₂)`. -/
structure NestedConditioningL2Setup
    (μ : Measure Ω) (Y : Ω → ℝ) (X₁ : Ω → β) (X₂ : Ω → γ) where
  isProbability : IsProbabilityMeasure μ
  measurable_finer : Measurable X₂
  sigmaFinite_trim : SigmaFinite (μ.trim (conditioningSpace_le measurable_finer))
  memLp_response : MemLp Y 2 μ
  nested : conditioningSpace X₁ ≤ conditioningSpace X₂

namespace ConditionalL2Setup

/-- Forget an L2 setup to the L1 setup it implies. -/
def toL1 {Y : Ω → ℝ} {X : Ω → β} (h : ConditionalL2Setup μ Y X) :
    ConditionalL1Setup μ Y X where
  isProbability := h.isProbability
  measurable_conditioning := h.measurable_conditioning
  sigmaFinite_trim := h.sigmaFinite_trim
  integrable_response := by
    haveI : IsProbabilityMeasure μ := h.isProbability
    exact h.memLp_response.integrable one_le_two

end ConditionalL2Setup

namespace NestedConditioningL2Setup

/-- Forget a nested L2 setup to the nested L1 setup it implies. -/
def toL1 {Y : Ω → ℝ} {X₁ : Ω → β} {X₂ : Ω → γ}
    (h : NestedConditioningL2Setup μ Y X₁ X₂) :
    NestedConditioningL1Setup μ Y X₁ X₂ where
  isProbability := h.isProbability
  measurable_finer := h.measurable_finer
  sigmaFinite_trim := h.sigmaFinite_trim
  integrable_response := by
    haveI : IsProbabilityMeasure μ := h.isProbability
    exact h.memLp_response.integrable one_le_two
  nested := h.nested

end NestedConditioningL2Setup

namespace ConditionalL1Setup

/-- Simple law of iterated expectations for a packaged conditioning setup. -/
theorem simple_law_iterated_expectation
    {Y : Ω → ℝ} {X : Ω → β} (h : ConditionalL1Setup μ Y X) :
    ∫ ω, condExpOn μ Y X ω ∂μ = ∫ ω, Y ω ∂μ := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [condExpOn, conditioningSpace] using
    HansenEconometrics.simple_law_iterated_expectation
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      (conditioningSpace_le h.measurable_conditioning)

/-- The CEF error has conditional mean zero. -/
theorem condExp_cefError_zero
    {Y : Ω → ℝ} {X : Ω → β} (h : ConditionalL1Setup μ Y X) :
    condExpOn μ (cefErrorOn μ Y X) X =ᵐ[μ] 0 := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [cefErrorOn_eq_cefError, condExpOn, conditioningSpace] using
    HansenEconometrics.condExp_cefError_zero
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      (conditioningSpace_le h.measurable_conditioning)
      h.integrable_response

/-- The CEF error has unconditional mean zero. -/
theorem integral_cefError_zero
    {Y : Ω → ℝ} {X : Ω → β} (h : ConditionalL1Setup μ Y X) :
    ∫ ω, cefErrorOn μ Y X ω ∂μ = 0 := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [cefErrorOn_eq_cefError, conditioningSpace] using
    HansenEconometrics.integral_cefError_zero
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      (conditioningSpace_le h.measurable_conditioning)
      h.integrable_response

/-- Pull a packaged `X`-measurable predictor through an integral. -/
theorem conditioning_integral
    {Y g : Ω → ℝ} {X : Ω → β}
    (h : ConditionalL1Setup μ Y X) (hg : XPredictorL1 μ X g)
    (hgY : Integrable (fun ω => g ω * Y ω) μ) :
    ∫ ω, g ω * Y ω ∂μ = ∫ ω, g ω * condExpOn μ Y X ω ∂μ := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [XMeasurable, condExpOn, conditioningSpace] using
    HansenEconometrics.conditioning_theorem_integral
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (g := g)
      (Y := Y)
      (conditioningSpace_le h.measurable_conditioning)
      hg.x_measurable
      hgY
      h.integrable_response

/-- The CEF error is orthogonal to an `X`-measurable predictor. -/
theorem integral_mul_cefError_zero
    {Y g : Ω → ℝ} {X : Ω → β}
    (h : ConditionalL1Setup μ Y X) (hg : XPredictorL1 μ X g)
    (hgE : Integrable (fun ω => g ω * cefErrorOn μ Y X ω) μ) :
    ∫ ω, g ω * cefErrorOn μ Y X ω ∂μ = 0 := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [XMeasurable, cefErrorOn_eq_cefError, conditioningSpace] using
    HansenEconometrics.integral_mul_cefError_zero
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (g := g)
      (Y := Y)
      (conditioningSpace_le h.measurable_conditioning)
      hg.x_measurable
      hgE
      h.integrable_response

end ConditionalL1Setup

namespace NestedConditioningL1Setup

/-- Tower property for a packaged nested conditioning setup. -/
theorem tower_property
    {Y : Ω → ℝ} {X₁ : Ω → β} {X₂ : Ω → γ}
    (h : NestedConditioningL1Setup μ Y X₁ X₂) :
    condExpOn μ (condExpOn μ Y X₂) X₁ =ᵐ[μ] condExpOn μ Y X₁ := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_finer)) :=
    h.sigmaFinite_trim
  simpa [condExpOn, conditioningSpace] using
    HansenEconometrics.tower_property
      (m₁ := conditioningSpace X₁)
      (m₂ := conditioningSpace X₂)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      h.nested
      (conditioningSpace_le h.measurable_finer)

end NestedConditioningL1Setup

namespace ConditionalL2Setup

/-- Conditional expectation is the best square-integrable `X`-measurable predictor. -/
theorem best_predictor
    {Y g : Ω → ℝ} {X : Ω → β}
    (h : ConditionalL2Setup μ Y X) (hg : XPredictorL2 μ X g) :
    ∫ ω, (Y ω - condExpOn μ Y X ω) ^ 2 ∂μ ≤ ∫ ω, (Y ω - g ω) ^ 2 ∂μ := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [condExpOn, XMeasurable, conditioningSpace] using
    HansenEconometrics.integral_sq_sub_condExp_le_integral_sq_sub_X
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      (g := g)
      (X := X)
      h.measurable_conditioning
      h.memLp_response
      hg.memLp_predictor
      hg.x_measurable

/-- Law of total variance for a packaged L2 setup. -/
theorem law_total_variance
    {Y : Ω → ℝ} {X : Ω → β} (h : ConditionalL2Setup μ Y X) :
    μ[condVarOn μ Y X] + Var[condExpOn μ Y X; μ] = Var[Y; μ] := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  simpa [condVarOn, condExpOn, conditioningSpace] using
    HansenEconometrics.law_total_variance
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      (conditioningSpace_le h.measurable_conditioning)
      h.memLp_response

/-- Variance decomposition for a packaged L2 setup. -/
theorem variance_decomposition
    {Y : Ω → ℝ} {X : Ω → β} (h : ConditionalL2Setup μ Y X) :
    Var[Y; μ] = μ[condVarOn μ Y X] + Var[condExpOn μ Y X; μ] := by
  rw [eq_comm]
  exact h.law_total_variance

/-- Explained variance is bounded by total variance. -/
theorem variance_condExp_le_variance
    {Y : Ω → ℝ} {X : Ω → β} (h : ConditionalL2Setup μ Y X) :
    Var[condExpOn μ Y X; μ] ≤ Var[Y; μ] := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  simpa [condExpOn, conditioningSpace] using
    HansenEconometrics.variance_condExp_le_variance
      (m := conditioningSpace X)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      (conditioningSpace_le h.measurable_conditioning)
      h.memLp_response

end ConditionalL2Setup

namespace NestedConditioningL2Setup

/-- Richer conditioning variables weakly reduce residual variance. -/
theorem residualVar_antitone
    {Y : Ω → ℝ} {X₁ : Ω → β} {X₂ : Ω → γ}
    (h : NestedConditioningL2Setup μ Y X₁ X₂) :
    residualVarOn μ Y X₂ ≤ residualVarOn μ Y X₁ := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  simpa [residualVarOn, conditioningSpace] using
    HansenEconometrics.variance_cefError_antitone
      (m₁ := conditioningSpace X₁)
      (m₂ := conditioningSpace X₂)
      (m₀ := inferInstance)
      (μ := μ)
      (Y := Y)
      h.nested
      (conditioningSpace_le h.measurable_finer)
      h.memLp_response

end NestedConditioningL2Setup

end HansenEconometrics
