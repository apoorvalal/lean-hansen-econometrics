import Mathlib

open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open MeasureTheory

namespace HansenEconometrics

variable {Ω β γ : Type*}
variable {m m₁ m₂ m₀ : MeasurableSpace Ω}
variable {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
variable {μ : Measure Ω}

/-- Hansen Chapter 2 CEF error: `e = Y - E[Y | m]`. -/
noncomputable def cefError (μ : Measure Ω) (Y : Ω → ℝ) (m : MeasurableSpace Ω) : Ω → ℝ :=
  fun ω => Y ω - (μ[Y | m]) ω

/-- Theorem 2.1, specialized to Mathlib notation: simple law of iterated expectations. -/
theorem simple_law_iterated_expectation
    {Y : Ω → ℝ}
    (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] :
    ∫ ω, (μ[Y | m]) ω ∂μ = ∫ ω, Y ω ∂μ := by
  simpa using (MeasureTheory.integral_condExp (m := m) (m₀ := m₀) (μ := μ) (f := Y) hm)

/-- Theorem 2.2: tower property for nested sigma-algebras. -/
theorem tower_property
    {Y : Ω → ℝ}
    (hm₁₂ : m₁ ≤ m₂)
    (hm₂₀ : m₂ ≤ m₀)
    [SigmaFinite (μ.trim hm₂₀)] :
    μ[μ[Y | m₂] | m₁] =ᵐ[μ] μ[Y | m₁] := by
  simpa using
    (MeasureTheory.condExp_condExp_of_le
      (m₁ := m₁) (m₂ := m₂) (m₀ := m₀) (μ := μ) (f := Y) hm₁₂ hm₂₀)

/-- Theorem 2.2 written as `E[E[Y | X₁, X₂] | X₁] = E[Y | X₁]`. -/
theorem tower_property_X1_X2
    {Y : Ω → ℝ} {X1 : Ω → β} {X2 : Ω → γ}
    (hX1 : Measurable X1)
    (hX2 : Measurable X2)
    [SigmaFinite (μ.trim (sup_le hX1.comap_le hX2.comap_le))] :
    μ[μ[Y | (mβ.comap X1) ⊔ (mγ.comap X2)] | (mβ.comap X1)] =ᵐ[μ] μ[Y | (mβ.comap X1)] := by
  simpa using
    (MeasureTheory.condExp_condExp_of_le
      (m₁ := mβ.comap X1)
      (m₂ := (mβ.comap X1) ⊔ (mγ.comap X2))
      (m₀ := m₀)
      (μ := μ)
      (f := Y)
      le_sup_left
      (sup_le hX1.comap_le hX2.comap_le))

/-- Theorem 2.3, a.e. version: pull out an `m`-measurable factor from conditional expectation. -/
theorem conditioning_theorem_ae
    {g Y : Ω → ℝ}
    (hg : AEStronglyMeasurable[m] g μ)
    (hgY : Integrable (fun ω => g ω * Y ω) μ)
    (hY : Integrable Y μ) :
    μ[(fun ω => g ω * Y ω) | m] =ᵐ[μ] fun ω => g ω * (μ[Y | m]) ω := by
  simpa using
    (MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
      (m := m) (μ := μ) (f := g) (g := Y) hg hgY hY)

/-- Theorem 2.3 integrated version: `E[gY] = E[g E[Y|m]]`. -/
theorem conditioning_theorem_integral
    {g Y : Ω → ℝ}
    (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)]
    (hg : AEStronglyMeasurable[m] g μ)
    (hgY : Integrable (fun ω => g ω * Y ω) μ)
    (hY : Integrable Y μ) :
    ∫ ω, g ω * Y ω ∂μ = ∫ ω, g ω * (μ[Y | m]) ω ∂μ := by
  rw [← MeasureTheory.integral_condExp (m := m) (m₀ := m₀) (μ := μ) (f := fun ω => g ω * Y ω) hm]
  refine integral_congr_ae ?_
  exact conditioning_theorem_ae (m := m) (μ := μ) hg hgY hY

/-- Theorem 2.4.1: the CEF error has conditional mean zero. -/
theorem condExp_cefError_zero
    {Y : Ω → ℝ}
    (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)]
    (hY : Integrable Y μ) :
    μ[cefError (μ := μ) Y m | m] =ᵐ[μ] 0 := by
  have hcond0 : μ[μ[Y | m] | m] = μ[Y | m] := by
    simpa using
      (MeasureTheory.condExp_of_stronglyMeasurable (m := m) (m₀ := m₀) (μ := μ)
        (f := μ[Y | m]) hm stronglyMeasurable_condExp integrable_condExp)
  have hcond : μ[μ[Y | m] | m] =ᵐ[μ] μ[Y | m] := by
    filter_upwards [] with ω
    simpa using congrFun hcond0 ω
  calc
    μ[cefError (μ := μ) Y m | m]
        =ᵐ[μ] μ[Y | m] - μ[μ[Y | m] | m] := by
          simpa [cefError] using
            (MeasureTheory.condExp_sub (μ := μ) (f := Y) (g := μ[Y | m]) hY integrable_condExp m)
    _ =ᵐ[μ] μ[Y | m] - μ[Y | m] := by
          filter_upwards [hcond] with ω hω
          simp [hω]
    _ =ᵐ[μ] 0 := by simp

/-- Theorem 2.4.2: the CEF error has unconditional mean zero. -/
theorem integral_cefError_zero
    {Y : Ω → ℝ}
    (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)]
    (hY : Integrable Y μ) :
    ∫ ω, cefError (μ := μ) Y m ω ∂μ = 0 := by
  rw [← MeasureTheory.integral_condExp (m := m) (m₀ := m₀) (μ := μ)
    (f := cefError (μ := μ) Y m) hm]
  rw [integral_congr_ae (condExp_cefError_zero (m := m) (m₀ := m₀) (μ := μ) hm hY)]
  simp

/-- Theorem 2.4.4: the CEF error is orthogonal to any `m`-measurable function. -/
theorem integral_mul_cefError_zero
    {g Y : Ω → ℝ}
    (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)]
    (hg : AEStronglyMeasurable[m] g μ)
    (hgE : Integrable (fun ω => g ω * cefError (μ := μ) Y m ω) μ)
    (hY : Integrable Y μ) :
    ∫ ω, g ω * cefError (μ := μ) Y m ω ∂μ = 0 := by
  rw [← MeasureTheory.integral_condExp (m := m) (m₀ := m₀) (μ := μ)
    (f := fun ω => g ω * cefError (μ := μ) Y m ω) hm]
  have hmul : μ[(fun ω => g ω * cefError (μ := μ) Y m ω) | m] =ᵐ[μ]
      (fun ω => g ω * μ[cefError (μ := μ) Y m | m] ω) :=
    conditioning_theorem_ae (m := m) (μ := μ) (g := g) (Y := cefError (μ := μ) Y m) hg hgE
      (hY.sub integrable_condExp)
  rw [integral_congr_ae hmul]
  rw [integral_congr_ae (by
    filter_upwards [condExp_cefError_zero (m := m) (m₀ := m₀) (μ := μ) hm hY] with ω hω
    change g ω * μ[cefError (μ := μ) Y m | m] ω = 0
    simp [hω])]
  simp

end HansenEconometrics
