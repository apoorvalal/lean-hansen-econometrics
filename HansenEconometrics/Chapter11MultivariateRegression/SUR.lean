import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter11MultivariateRegression.Asymptotics

/-!
# Chapter 11 — seemingly unrelated regression

This module records the SUR/GLS estimator and covariance surface used by the
Hansen Theorems 11.4--11.6 formalization route. It includes deterministic
bridges to Chapter 4 GLS, inverse-CMT covariance consistency, and the fixed
inverse-covariance WLLN specialization plus an estimated-inverse covariance
perturbation wrapper for the fully feasible SUR information matrix.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (Matrix ι κ ℝ) :=
  matrixBorelMeasurableSpace ι κ

private lemma matrixBorelSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    @BorelSpace (Matrix ι κ ℝ) _ (matrixBorelMeasurableSpaceInst (ι := ι) (κ := κ)) :=
  matrixBorelSpace ι κ

attribute [local instance] matrixBorelMeasurableSpaceInst matrixBorelSpaceInst

variable {Ω k : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype k] [DecidableEq k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- SUR asymptotic variance `(E[X'Σ⁻¹X])⁻¹`. -/
noncomputable def surAsymptoticVariance (M : Matrix k k ℝ) : Matrix k k ℝ :=
  M⁻¹

/-- Feasible SUR variance estimator surface. -/
noncomputable def surVarianceEstimator (Mhat : Matrix k k ℝ) : Matrix k k ℝ :=
  Mhat⁻¹

omit [DecidableEq n] in
/-- Weighted SUR score mean `n⁻¹∑ Xᵢ'W Yᵢ`, where `W` is typically
`Σ̂⁻¹` or `Σ⁻¹`. -/
noncomputable def surWeightedScoreMean
    (X : n → Matrix m k ℝ) (W : Matrix m m ℝ) (Y : n → m → ℝ) : k → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, (X i)ᵀ *ᵥ (W *ᵥ Y i)

omit [DecidableEq n] in
/-- Hansen feasible SUR estimator written at the observation-system level:
`(n⁻¹∑ Xᵢ'W Xᵢ)⁻¹ (n⁻¹∑ Xᵢ'W Yᵢ)`. -/
noncomputable def surBetaFromInverseCovStar
    (X : n → Matrix m k ℝ) (W : Matrix m m ℝ) (Y : n → m → ℝ) : k → ℝ :=
  (systemHomoskedasticMiddle X W)⁻¹ *ᵥ surWeightedScoreMean X W Y

omit [DecidableEq n] in
/-- Hansen residual covariance estimator `n⁻¹∑ êᵢêᵢ'`, reused by feasible SUR. -/
noncomputable def surResidualCovariance (ehat : n → m → ℝ) : Matrix m m ℝ :=
  systemSigmaHat ehat

/-- Totalized SUR/GLS estimator, using `Matrix.nonsingInv` for both inverses. -/
noncomputable def surBetaStar
    (X : Matrix n k ℝ) (Ωmat : Matrix n n ℝ) (y : n → ℝ) : k → ℝ :=
  (Xᵀ * Ωmat⁻¹ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (Ωmat⁻¹ *ᵥ y))

/-- On nonsingular inputs, the totalized SUR estimator agrees with the Chapter 4 GLS estimator. -/
theorem surBetaStar_eq_glsBeta
    (X : Matrix n k ℝ) (Ωmat : Matrix n n ℝ) (y : n → ℝ)
    [Invertible Ωmat] [Invertible (Xᵀ * ⅟Ωmat * X)] :
    surBetaStar X Ωmat y = glsBeta X Ωmat y := by
  unfold surBetaStar glsBeta
  rw [← invOf_eq_nonsing_inv Ωmat]
  rw [← invOf_eq_nonsing_inv (Xᵀ * ⅟Ωmat * X)]

/-- Interface projection for SUR asymptotic normality. -/
theorem sur_gaussianLimit_from_interface
    (T : ℕ → Ω → k → ℝ) (M : Matrix k k ℝ)
    (hT : GaussianLimit μ T (surAsymptoticVariance M)) :
    GaussianLimit μ T (surAsymptoticVariance M) :=
  hT

/-- Distributional face of `sur_gaussianLimit_from_interface`. -/
theorem sur_tendstoInDistribution_from_interface
    (T : ℕ → Ω → k → ℝ) (M : Matrix k k ℝ)
    (hT : GaussianLimit μ T (surAsymptoticVariance M)) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (surAsymptoticVariance M)) :=
  hT.limit

omit [Fintype k] [DecidableEq k] in
/-- Loewner-order bridge for SUR efficiency once the variance gap has been
established by a concrete SUR proof. -/
theorem sur_efficiency_from_loewner_gap
    (Vsur Vols : Matrix k k ℝ) (h : (Vols - Vsur).PosSemidef) :
    (Vols - Vsur).PosSemidef :=
  h

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Deterministic GLS variance-gap bridge behind Hansen Theorem 11.5.

This specializes the Chapter 4 generalized Gauss-Markov variance-gap theorem to
the SUR/GLS covariance notation `(Xᵀ Ω⁻¹ X)⁻¹`. -/
theorem sur_efficiency_from_gls_variance_gap
    (X A : Matrix n k ℝ) (Ωmat : Matrix n n ℝ)
    [Invertible Ωmat] [Invertible (Xᵀ * ⅟Ωmat * X)]
    (hΩ : Ωmat.PosSemidef)
    (hAX : Aᵀ * X = (1 : Matrix k k ℝ)) :
    (Aᵀ * Ωmat * A - surAsymptoticVariance (Xᵀ * ⅟Ωmat * X)).PosSemidef := by
  simpa [surAsymptoticVariance, invOf_eq_nonsing_inv] using
    generalizedGaussMarkov_variance_gap_posSemidef X A Ωmat hΩ hAX

omit [IsProbabilityMeasure μ] [DecidableEq k] in
/-- Interface projection for feasible SUR covariance consistency. -/
theorem surCovariance_consistent_from_interface
    (Vhat : ℕ → Ω → Matrix k k ℝ) (Vsur : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent μ Vhat Vsur) :
    CovarianceEstimatorConsistent μ Vhat Vsur :=
  hV

omit [DecidableEq n] in
/-- CMT for the SUR variance estimator `M̂⁻¹`.

Once the feasible SUR information matrix `M̂` converges to a nonsingular
population information matrix `M`, the inverse plug-in variance estimator
converges to `(M)⁻¹`. -/
theorem surVarianceEstimator_tendstoInMeasure
    {Mhat : ℕ → Ω → Matrix k k ℝ} {M : Matrix k k ℝ}
    (hM_meas : ∀ t, AEStronglyMeasurable (Mhat t) μ)
    (hM : TendstoInMeasure μ Mhat atTop (fun _ => M))
    (hM_unit : IsUnit M.det) :
    TendstoInMeasure μ
      (fun t ω => surVarianceEstimator (Mhat t ω))
      atTop (fun _ => surAsymptoticVariance M) := by
  simpa [surVarianceEstimator, surAsymptoticVariance] using
    tendstoInMeasure_matrix_inv hM_meas hM (fun _ => hM_unit)

omit [DecidableEq n] in
/-- Feasible SUR covariance-consistency wrapper from inverse-CMT consistency of
the information matrix. -/
theorem surCovariance_consistent_of_information_tendsto
    {Mhat : ℕ → Ω → Matrix k k ℝ} {M : Matrix k k ℝ}
    (hM_meas : ∀ t, AEStronglyMeasurable (Mhat t) μ)
    (hM : TendstoInMeasure μ Mhat atTop (fun _ => M))
    (hM_unit : IsUnit M.det) :
    CovarianceEstimatorConsistent μ
      (fun t ω => surVarianceEstimator (Mhat t ω))
      (surAsymptoticVariance M) := by
  refine covarianceEstimatorConsistent_of_tendstoInMeasure _ _ ?hmeas ?hconv
  · intro t
    exact aestronglyMeasurable_matrix_inv (hM_meas t)
  · exact surVarianceEstimator_tendstoInMeasure hM_meas hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Fixed-inverse-covariance WLLN route for feasible SUR covariance consistency.

This specializes the Chapter 11 homoskedastic middle WLLN to the SUR
information matrix `E[X_i'Σ⁻¹X_i]` and then applies inverse-CMT consistency for
`M̂⁻¹`. The fully feasible case with estimated `Σ̂` requires a separate
perturbation theorem for `Σ̂⁻¹` inside the middle matrix. -/
theorem surCovariance_consistent_of_fixed_inverse_cov_wlln
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surVarianceEstimator
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovariance_consistent_of_information_tendsto
    (μ := μ)
    (Mhat := fun t ω =>
      systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)
    (M := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])
    (fun t =>
      systemHomoskedasticMiddle_fixed_aestronglyMeasurable
        (μ := μ) Sigma⁻¹ hint hident t)
    (systemHomoskedasticMiddle_fixed_tendstoInMeasure
      (μ := μ) Sigma⁻¹ hint hindep hident)
    hM_unit

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Estimated-inverse-covariance route for Hansen Theorem 11.6.

Here `SigmaInv` is the population inverse covariance matrix and `SigmaInvHat`
is the feasible inverse covariance sequence appearing in
`n⁻¹∑ X_i' SigmaInvHat X_i`. Once that feasible information matrix differs
from the fixed-`SigmaInv` matrix by `o_p(1)`, inverse-CMT gives consistency of
the SUR covariance estimator. -/
theorem surCovariance_consistent_of_estimated_inverse_cov_substitution
    {X : ℕ → Ω → Matrix m k ℝ} (SigmaInv : Matrix m m ℝ)
    {SigmaInvHat : ℕ → Ω → Matrix m m ℝ}
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) SigmaInv) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) SigmaInv)))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) SigmaInv)
        (fun ω => systemMiddleTerm (X 0 ω) SigmaInv) μ μ)
    (hMhat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω)) μ)
    (hsub : TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) (SigmaInvHat t ω) -
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) SigmaInv)
      atTop (fun _ => 0))
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) SigmaInv]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surVarianceEstimator
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) SigmaInv])) :=
  surCovariance_consistent_of_information_tendsto
    (μ := μ)
    (Mhat := fun t ω =>
      systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) (SigmaInvHat t ω))
    (M := μ[fun ω => systemMiddleTerm (X 0 ω) SigmaInv])
    hMhat_meas
    (systemHomoskedasticMiddle_feasible_tendstoInMeasure_of_substitution
      (systemHomoskedasticMiddle_fixed_tendstoInMeasure
        (μ := μ) SigmaInv hint hindep hident)
      hsub)
    hM_unit

end HansenEconometrics
