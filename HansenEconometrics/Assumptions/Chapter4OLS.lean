import HansenEconometrics.Chapter4LeastSquaresRegression

/-!
# Chapter 4 Fixed-Design OLS Setups

This module packages the repeated fixed-design OLS conditioning hypotheses from
Chapter 4. The methods wrap the sigma-algebra backend theorems in
`Chapter4LeastSquaresRegression`.
-/

open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open MeasureTheory ProbabilityTheory Matrix

namespace HansenEconometrics

variable {Ω ζ n k : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace ζ]
variable [Fintype n] [Fintype k] [DecidableEq k]
variable {μ : Measure Ω}

/-- Fixed-design OLS setup with conditional mean-zero errors. -/
structure FixedDesignOLSCondMeanZeroSetup
    (μ : Measure Ω) (X : Matrix n k ℝ) (e : Ω → n → ℝ)
    (β : k → ℝ) (Z : Ω → ζ) where
  isProbability : IsProbabilityMeasure μ
  measurable_conditioning : Measurable Z
  sigmaFinite_trim : SigmaFinite (μ.trim (conditioningSpace_le measurable_conditioning))
  error_integrable : ∀ i, Integrable (fun ω => e ω i) μ
  cond_error_zero : ∀ i, condExpOn μ (fun ω => e ω i) Z =ᵐ[μ] 0

/-- Fixed-design OLS setup with conditional second moments. -/
structure FixedDesignOLSCondSecondMomentSetup
    (μ : Measure Ω) (X : Matrix n k ℝ) (e : Ω → n → ℝ)
    (β : k → ℝ) (Z : Ω → ζ) (D : Matrix n n ℝ)
    extends FixedDesignOLSCondMeanZeroSetup μ X e β Z where
  second_integrable : ∀ i r, Integrable (fun ω => e ω i * e ω r) μ
  cond_second_moment :
    ∀ i r, condExpOn μ (fun ω => e ω i * e ω r) Z =ᵐ[μ] fun _ => D i r

namespace FixedDesignOLSCondMeanZeroSetup

/-- Componentwise conditional unbiasedness of OLS. -/
theorem condExp_coordinate_eq_beta
    {X : Matrix n k ℝ} {e : Ω → n → ℝ} {β : k → ℝ} {Z : Ω → ζ}
    [Invertible (Xᵀ * X)]
    (h : FixedDesignOLSCondMeanZeroSetup μ X e β Z) (j : k) :
    condExpOn μ (fun ω => olsBeta X (X *ᵥ β + e ω) j) Z =ᵐ[μ] fun _ => β j := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [condExpOn, conditioningSpace] using
    ols_condExp_coordinate_eq_beta
      (μ := μ)
      (m := conditioningSpace Z)
      (m₀ := inferInstance)
      X β e j
      (conditioningSpace_le h.measurable_conditioning)
      h.error_integrable
      (fun i => by simpa [condExpOn, conditioningSpace] using h.cond_error_zero i)

/-- Vector-valued conditional unbiasedness of OLS. -/
theorem condExp_eq_beta
    {X : Matrix n k ℝ} {e : Ω → n → ℝ} {β : k → ℝ} {Z : Ω → ζ}
    [Invertible (Xᵀ * X)]
    (h : FixedDesignOLSCondMeanZeroSetup μ X e β Z) :
    condExpOn μ (fun ω => olsBeta X (X *ᵥ β + e ω)) Z =ᵐ[μ] fun _ => β := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [condExpOn, conditioningSpace] using
    ols_condExp_eq_beta
      (μ := μ)
      (m := conditioningSpace Z)
      (m₀ := inferInstance)
      X β e
      (conditioningSpace_le h.measurable_conditioning)
      h.error_integrable
      (fun i => by simpa [condExpOn, conditioningSpace] using h.cond_error_zero i)

/-- Componentwise unconditional unbiasedness of OLS. -/
theorem integral_coordinate_eq_beta
    {X : Matrix n k ℝ} {e : Ω → n → ℝ} {β : k → ℝ} {Z : Ω → ζ}
    [Invertible (Xᵀ * X)]
    (h : FixedDesignOLSCondMeanZeroSetup μ X e β Z) (j : k) :
    ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ = β j := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  exact ols_integral_coordinate_eq_beta
    (μ := μ)
    (m := conditioningSpace Z)
    (m₀ := inferInstance)
    X β e j
    (conditioningSpace_le h.measurable_conditioning)
    h.error_integrable
    (fun i => by simpa [condExpOn, conditioningSpace] using h.cond_error_zero i)

/-- Vector-valued unconditional unbiasedness of OLS. -/
theorem integral_eq_beta
    {X : Matrix n k ℝ} {e : Ω → n → ℝ} {β : k → ℝ} {Z : Ω → ζ}
    [Invertible (Xᵀ * X)]
    (h : FixedDesignOLSCondMeanZeroSetup μ X e β Z) :
    ∫ ω, olsBeta X (X *ᵥ β + e ω) ∂μ = β := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  exact ols_integral_eq_beta
    (μ := μ)
    (m := conditioningSpace Z)
    (m₀ := inferInstance)
    X β e
    (conditioningSpace_le h.measurable_conditioning)
    h.error_integrable
    (fun i => by simpa [condExpOn, conditioningSpace] using h.cond_error_zero i)

end FixedDesignOLSCondMeanZeroSetup

namespace FixedDesignOLSCondSecondMomentSetup

/-- Matrix-valued conditional covariance bridge for fixed-design OLS. -/
theorem condExp_centered_mul_eq_variance_matrix
    {X : Matrix n k ℝ} {e : Ω → n → ℝ} {β : k → ℝ} {Z : Ω → ζ}
    {D : Matrix n n ℝ}
    [Invertible (Xᵀ * X)]
    (h : FixedDesignOLSCondSecondMomentSetup μ X e β Z D) :
    condExpOn μ
        (fun ω => fun j l =>
          (olsBeta X (X *ᵥ β + e ω) j - β j) *
            (olsBeta X (X *ᵥ β + e ω) l - β l))
        Z =ᵐ[μ]
      fun _ => olsConditionalVarianceMatrix X D := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  simpa [condExpOn, conditioningSpace] using
    ols_condExp_centered_mul_eq_variance_matrix
      (μ := μ)
      (m := conditioningSpace Z)
      (m₀ := inferInstance)
      X β e D
      (conditioningSpace_le h.measurable_conditioning)
      h.second_integrable
      (fun i r => by simpa [condExpOn, conditioningSpace] using h.cond_second_moment i r)

/-- Matrix-valued unconditional covariance bridge for fixed-design OLS. -/
theorem integral_centered_mul_eq_variance_matrix
    {X : Matrix n k ℝ} {e : Ω → n → ℝ} {β : k → ℝ} {Z : Ω → ζ}
    {D : Matrix n n ℝ}
    [Invertible (Xᵀ * X)]
    (h : FixedDesignOLSCondSecondMomentSetup μ X e β Z D) :
    ∫ ω, (fun j l =>
      (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l)) ∂μ =
      olsConditionalVarianceMatrix X D := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.measurable_conditioning)) :=
    h.sigmaFinite_trim
  exact ols_integral_centered_mul_eq_variance_matrix
    (μ := μ)
    (m := conditioningSpace Z)
    (m₀ := inferInstance)
    X β e D
    (conditioningSpace_le h.measurable_conditioning)
    h.second_integrable
    (fun i r => by simpa [condExpOn, conditioningSpace] using h.cond_second_moment i r)

end FixedDesignOLSCondSecondMomentSetup

end HansenEconometrics
