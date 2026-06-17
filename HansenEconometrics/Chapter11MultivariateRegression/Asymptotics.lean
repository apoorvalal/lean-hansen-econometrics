import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter11MultivariateRegression.Systems

/-!
# Chapter 11 — asymptotic regression-system interfaces

This file records the reusable Chapter 7/8 convergence layer needed by the
Chapter 11 regression-system theorems. It includes non-tautological
stacked-system wrappers for Theorems 11.1--11.2, exact system-matrix WLLN/CMT
assembly for the Theorem 11.3 covariance route, and compatibility projections
for theorem surfaces whose primitive assumptions are supplied elsewhere.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

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

variable {Ω k q : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Interface projection for system least-squares asymptotic normality. -/
theorem systemLeastSquares_gaussianLimit_from_interface
    (T : ℕ → Ω → k → ℝ) (Q Ωmat : Matrix k k ℝ)
    (hT : GaussianLimit μ T (systemAsymptoticVariance Q Ωmat)) :
    GaussianLimit μ T (systemAsymptoticVariance Q Ωmat) :=
  hT

/-- Distributional face of `systemLeastSquares_gaussianLimit_from_interface`. -/
theorem systemLeastSquares_tendstoInDistribution_from_interface
    (T : ℕ → Ω → k → ℝ) (Q Ωmat : Matrix k k ℝ)
    (hT : GaussianLimit μ T (systemAsymptoticVariance Q Ωmat)) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemAsymptoticVariance Q Ωmat)) :=
  hT.limit

/-- **Hansen Theorem 11.1, stacked-system Star estimator.**

System least squares is ordinary least squares on the stacked system, so the
Chapter 7 totalized OLS CLT applies directly. The covariance is restated using
Chapter 11's `systemAsymptoticVariance` notation. -/
theorem systemLeastSquaresBetaStar_tendstoInDistribution_heteroAsymCov
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) •
        (systemLeastSquaresBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e))) := by
  simpa [systemLeastSquaresBetaStar, systemAsymptoticVariance, heteroAsymCov] using
    olsBetaStar_vector_tendstoInDistribution_heteroAsymCov
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel

/-- **Hansen Theorem 11.2, fixed-derivative linear transform.**

Applying a fixed derivative matrix `Rᵀ` to the stacked-system Star estimator's
Chapter 11.1 Gaussian limit gives Hansen's delta-method covariance
`Vθ = Rᵀ Vβ R`. -/
theorem systemLeastSquaresBetaStar_linearTransform_tendstoInDistribution
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ) (R : Matrix k q ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) •
        (Rᵀ *ᵥ systemLeastSquaresBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) -
          Rᵀ *ᵥ β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)) R)) := by
  let T : ℕ → Ω → k → ℝ := fun n ω =>
    Real.sqrt (n : ℝ) •
      (systemLeastSquaresBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
  let Te : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (T n ω)
  have hT := systemLeastSquaresBetaStar_tendstoInDistribution_heteroAsymCov
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hTe :
      TendstoInDistribution Te atTop (fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ)
        (multivariateGaussian 0
          (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e))) := by
    have hmap := hT.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [T, Te, Function.comp_def] using hmap
  have hS : (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)).PosSemidef := by
    simpa [systemAsymptoticVariance, heteroAsymCov] using
      heteroAsymCov_posSemidef (μ := μ) (X := X) (e := e) h
  have hlin :
      TendstoInDistribution
        (fun n => matrixContinuousLinearMap Rᵀ ∘ Te n)
        atTop (matrixContinuousLinearMap Rᵀ ∘ fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ)
        (multivariateGaussian 0
          (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e))) :=
    hTe.continuous_comp (matrixContinuousLinearMap Rᵀ).continuous
  have hLaw :
      HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap Rᵀ z)
        (multivariateGaussian 0
          (systemDeltaVariance
            (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)) R))
        (multivariateGaussian 0
          (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e))) := by
    simpa [systemDeltaVariance, matrixContinuousLinearMap,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := q) hS Rᵀ
  have htargetE :
      TendstoInDistribution
        (fun n ω => matrixContinuousLinearMap Rᵀ (Te n ω))
        atTop (fun z : EuclideanSpace ℝ q => z)
        (fun _ => μ)
        (multivariateGaussian 0
          (systemDeltaVariance
            (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)) R)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ q) hlin hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : q => ℝ))
  simpa [T, Te, Function.comp_def, matrixContinuousLinearMap_apply] using htarget

omit [DecidableEq k] in
/-- Interface projection for delta-method asymptotic normality of smooth
functions of multiple-equation coefficients. -/
theorem systemDelta_gaussianLimit_from_interface
    (Tθ : ℕ → Ω → q → ℝ) (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTθ : GaussianLimit μ Tθ (systemDeltaVariance Vβ R)) :
    GaussianLimit μ Tθ (systemDeltaVariance Vβ R) :=
  hTθ

omit [DecidableEq k] in
/-- Distributional face of `systemDelta_gaussianLimit_from_interface`. -/
theorem systemDelta_tendstoInDistribution_from_interface
    (Tθ : ℕ → Ω → q → ℝ) (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTθ : GaussianLimit μ Tθ (systemDeltaVariance Vβ R)) :
    TendstoInDistribution Tθ atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) :=
  hTθ.limit

omit [IsProbabilityMeasure μ] [DecidableEq k] in
/-- Interface projection for a pair of system least-squares covariance
consistency statements. -/
theorem systemCovariance_consistent_from_interfaces
    (Vhat Vhat0 : ℕ → Ω → Matrix k k ℝ) (Vβ Vβ0 : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent μ Vhat Vβ)
    (hV0 : CovarianceEstimatorConsistent μ Vhat0 Vβ0) :
    CovarianceEstimatorConsistent μ Vhat Vβ ∧
      CovarianceEstimatorConsistent μ Vhat0 Vβ0 :=
  ⟨hV, hV0⟩

omit [DecidableEq k] [DecidableEq m] in
/-- **System moment WLLN for Hansen Chapter 11.**

The normalized system Gram matrix `n⁻¹∑ Xᵢ'Xᵢ` converges to its population
counterpart under the Banach-valued WLLN hypotheses. -/
theorem systemNormalizedGram_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ}
    (hint : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ) :
    TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => μ[fun ω => (X 0 ω)ᵀ * X 0 ω]) := by
  have h :
      TendstoInMeasure μ
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, (X i ω)ᵀ * X i ω))
        atTop (fun _ => μ[fun ω => (X 0 ω)ᵀ * X 0 ω]) :=
    tendstoInMeasure_wlln
      (μ := μ) (fun i ω => (X i ω)ᵀ * X i ω) hint hindep hident
  have hfun_eq :
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) =
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, (X i ω)ᵀ * X i ω)) := by
    funext n ω
    have hsum :
        (∑ i : Fin n, (X i.val ω)ᵀ * X i.val ω) =
          ∑ i ∈ Finset.range n, (X i ω)ᵀ * X i ω :=
      Fin.sum_univ_eq_sum_range (fun i => (X i ω)ᵀ * X i ω) n
    simp only [systemNormalizedGram, Fintype.card_fin]
    rw [hsum]
  rw [hfun_eq]
  exact h

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Measurability of the normalized system Gram under the corresponding
identical-distribution moment hypotheses. -/
theorem systemNormalizedGram_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ}
    (hint : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ := by
  simp only [systemNormalizedGram]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((hident i.val).integrable_iff.mpr hint).aestronglyMeasurable

omit [DecidableEq k] [DecidableEq m] in
/-- **Ideal robust system-middle WLLN for Hansen Chapter 11.**

The normalized middle matrix `n⁻¹∑ Xᵢ'eᵢeᵢ'Xᵢ` converges to its population
counterpart under the Banach-valued WLLN hypotheses. This is the true-error
middle layer; replacing `eᵢ` by least-squares residuals is a separate feasible
residual-substitution step. -/
theorem systemRobustMiddle_ideal_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hint : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
        (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) := by
  have h :
      TendstoInMeasure μ
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω)))
        atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) :=
    tendstoInMeasure_wlln
      (μ := μ) (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))
      hint hindep hident
  have hfun_eq :
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω)) =
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω))) := by
    funext n ω
    have hsum :
        (∑ i : Fin n, systemRobustMiddleTerm (X i.val ω) (e i.val ω)) =
          ∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω) :=
      Fin.sum_univ_eq_sum_range
        (fun i => systemRobustMiddleTerm (X i ω) (e i ω)) n
    simp only [systemRobustMiddle, Fintype.card_fin]
    rw [hsum]
  rw [hfun_eq]
  exact h

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Measurability of the true-error robust system middle matrix under the
corresponding identical-distribution moment hypotheses. -/
theorem systemRobustMiddle_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hint : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
        (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω)) μ := by
  simp only [systemRobustMiddle]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((hident i.val).integrable_iff.mpr hint).aestronglyMeasurable

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Feasible-residual perturbation target for Hansen Theorem 11.3.

If replacing the true vector errors by feasible residuals changes the exact
system robust middle matrix by `o_p(1)`, then the feasible middle has the same
probability limit as the true-error middle. -/
theorem systemRobustMiddle_feasible_tendstoInMeasure_of_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e ehat : ℕ → Ω → m → ℝ}
    {Omega : Matrix k k ℝ}
    (hideal : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => Omega))
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω) -
          systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω))
      atTop (fun _ => Omega) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hsub hideal

omit [DecidableEq k] [DecidableEq m] in
/-- **Fixed-covariance homoskedastic system-middle WLLN for Hansen Chapter 11.**

For a fixed error covariance matrix `Σ`, the normalized middle matrix
`n⁻¹∑ Xᵢ'ΣXᵢ` converges to its population counterpart under the Banach-valued
WLLN hypotheses. -/
theorem systemHomoskedasticMiddle_fixed_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ) :
    TendstoInMeasure μ
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) := by
  have h :
      TendstoInMeasure μ
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemMiddleTerm (X i ω) Sigma))
        atTop (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
    tendstoInMeasure_wlln
      (μ := μ) (fun i ω => systemMiddleTerm (X i ω) Sigma)
      hint hindep hident
  have hfun_eq :
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma) =
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemMiddleTerm (X i ω) Sigma)) := by
    funext n ω
    have hsum :
        (∑ i : Fin n, systemMiddleTerm (X i.val ω) Sigma) =
          ∑ i ∈ Finset.range n, systemMiddleTerm (X i ω) Sigma :=
      Fin.sum_univ_eq_sum_range (fun i => systemMiddleTerm (X i ω) Sigma) n
    simp only [systemHomoskedasticMiddle, Fintype.card_fin]
    rw [hsum]
  rw [hfun_eq]
  exact h

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Measurability of the fixed-covariance homoskedastic system middle matrix. -/
theorem systemHomoskedasticMiddle_fixed_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma) μ := by
  simp only [systemHomoskedasticMiddle]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((hident i.val).integrable_iff.mpr hint).aestronglyMeasurable

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Estimated-covariance perturbation target for Hansen's homoskedastic system
middle matrix.

If replacing a fixed covariance matrix by an estimated matrix changes
`n⁻¹∑ Xᵢ'ΣXᵢ` by `o_p(1)`, then the estimated middle has the same probability
limit as the fixed-covariance middle. -/
theorem systemHomoskedasticMiddle_feasible_tendstoInMeasure_of_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {Sigma : Matrix m m ℝ}
    {SigmaHat : ℕ → Ω → Matrix m m ℝ} {Omega : Matrix k k ℝ}
    (hfixed : TendstoInMeasure μ
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => Omega))
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω) -
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop (fun _ => Omega) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hsub hfixed

/-- Continuous-mapping theorem for the normalized Chapter 11 sandwich covariance
`Q̂⁻¹Ω̂Q̂⁻¹`. -/
theorem systemSandwichCovariance_tendstoInMeasure
    {Qhat Omegahat : ℕ → Ω → Matrix k k ℝ} {Q Omega : Matrix k k ℝ}
    (hQ_meas : ∀ n, AEStronglyMeasurable (Qhat n) μ)
    (hOmega_meas : ∀ n, AEStronglyMeasurable (Omegahat n) μ)
    (hQ : TendstoInMeasure μ Qhat atTop (fun _ => Q))
    (hOmega : TendstoInMeasure μ Omegahat atTop (fun _ => Omega))
    (hQ_unit : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun n ω => systemSandwichCovariance (Qhat n ω) (Omegahat n ω))
      atTop (fun _ => systemAsymptoticVariance Q Omega) := by
  have hQinv : TendstoInMeasure μ
      (fun n ω => (Qhat n ω)⁻¹) atTop (fun _ => Q⁻¹) :=
    tendstoInMeasure_matrix_inv hQ_meas hQ (fun _ => hQ_unit)
  have hQinv_meas : ∀ n, AEStronglyMeasurable (fun ω => (Qhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hQ_meas n)
  have hLeft : TendstoInMeasure μ
      (fun n ω => (Qhat n ω)⁻¹ * Omegahat n ω)
      atTop (fun _ => Q⁻¹ * Omega) :=
    tendstoInMeasure_matrix_mul hQinv_meas hOmega_meas hQinv hOmega
  have hLeft_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (Qhat n ω)⁻¹ * Omegahat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQinv_meas n).prodMk (hOmega_meas n))
  have hFull : TendstoInMeasure μ
      (fun n ω => ((Qhat n ω)⁻¹ * Omegahat n ω) * (Qhat n ω)⁻¹)
      atTop (fun _ => (Q⁻¹ * Omega) * Q⁻¹) :=
    tendstoInMeasure_matrix_mul hLeft_meas hQinv_meas hLeft hQinv
  simpa [systemSandwichCovariance, systemAsymptoticVariance, Matrix.mul_assoc] using hFull

omit [DecidableEq m] in
/-- Moment-convergence route for the exact normalized robust system covariance
`Q̂⁻¹Ω̂Q̂⁻¹`. This is the CMT layer used by Hansen Theorem 11.3 after the
feasible residual middle matrix has been shown to converge. -/
theorem systemRobustCovariance_tendstoInMeasure_of_moment_convergence
    {X : ℕ → Ω → Matrix m k ℝ} {ehat : ℕ → Ω → m → ℝ}
    {Q Omega : Matrix k k ℝ}
    (hQ_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ)
    (hOmega_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω)) μ)
    (hQ : TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q))
    (hOmega : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω))
      atTop (fun _ => Omega))
    (hQ_unit : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovariance (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω))
      atTop (fun _ => systemAsymptoticVariance Q Omega) :=
  systemSandwichCovariance_tendstoInMeasure
    (μ := μ)
    (Qhat := fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
    (Omegahat := fun n ω =>
      systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω))
    hQ_meas hOmega_meas hQ hOmega hQ_unit

omit [DecidableEq m] in
/-- WLLN plus CMT route for the exact true-error robust system covariance
`Q̂⁻¹Ω̂Q̂⁻¹`. This proves the Hansen 11.3 sandwich shape for the ideal middle
matrix `n⁻¹∑ Xᵢ'eᵢeᵢ'Xᵢ`; feasible residual substitution is the remaining
separate step for `êᵢ`. -/
theorem systemRobustCovariance_tendstoInMeasure_of_ideal_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hQ_int : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hQ_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hQ_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ)
    (hOmega_int : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hOmega_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))))
    (hOmega_ident : ∀ i,
      IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
        (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ)
    (hQ_unit : IsUnit (μ[fun ω => (X 0 ω)ᵀ * X 0 ω]).det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovariance (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop
      (fun _ => systemAsymptoticVariance
        (μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
        (μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)])) :=
  systemRobustCovariance_tendstoInMeasure_of_moment_convergence
    (μ := μ)
    (X := X) (ehat := e)
    (Q := μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
    (Omega := μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)])
    (fun n => systemNormalizedGram_aestronglyMeasurable hQ_int hQ_ident n)
    (fun n => systemRobustMiddle_aestronglyMeasurable hOmega_int hOmega_ident n)
    (systemNormalizedGram_tendstoInMeasure hQ_int hQ_indep hQ_ident)
    (systemRobustMiddle_ideal_tendstoInMeasure hOmega_int hOmega_indep hOmega_ident)
    hQ_unit

omit [DecidableEq m] in
/-- Feasible-residual robust covariance route for Hansen Theorem 11.3.

This combines the exact true-error WLLN with a residual-substitution bound
`Ω̂_HC(ê) - Ω̂_HC(e) = o_p(1)`. It is the vector-system analogue of the
Chapter 7 HC covariance assembly, stated at the exact matrix level Hansen uses. -/
theorem systemRobustCovariance_tendstoInMeasure_of_feasible_wlln_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e ehat : ℕ → Ω → m → ℝ}
    (hQ_int : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hQ_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hQ_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ)
    (hOmega_int : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hOmega_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))))
    (hOmega_ident : ∀ i,
      IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
        (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ)
    (hOmega_hat_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => ehat i.val ω)) μ)
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω) -
          systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0))
    (hQ_unit : IsUnit (μ[fun ω => (X 0 ω)ᵀ * X 0 ω]).det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovariance (fun i : Fin n => X i.val ω)
          (fun i : Fin n => ehat i.val ω))
      atTop
      (fun _ => systemAsymptoticVariance
        (μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
        (μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)])) := by
  have hQ :
      TendstoInMeasure μ
        (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
        atTop (fun _ => μ[fun ω => (X 0 ω)ᵀ * X 0 ω]) :=
    systemNormalizedGram_tendstoInMeasure hQ_int hQ_indep hQ_ident
  have hOmegaIdeal :
      TendstoInMeasure μ
        (fun n ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω))
        atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) :=
    systemRobustMiddle_ideal_tendstoInMeasure hOmega_int hOmega_indep hOmega_ident
  have hOmegaHat :
      TendstoInMeasure μ
        (fun n ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => ehat i.val ω))
        atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) :=
    systemRobustMiddle_feasible_tendstoInMeasure_of_substitution hOmegaIdeal hsub
  exact systemRobustCovariance_tendstoInMeasure_of_moment_convergence
    (μ := μ)
    (X := X) (ehat := ehat)
    (Q := μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
    (Omega := μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)])
    (fun n => systemNormalizedGram_aestronglyMeasurable hQ_int hQ_ident n)
    hOmega_hat_meas hQ hOmegaHat hQ_unit

omit [DecidableEq m] in
/-- Moment-convergence route for the exact normalized homoskedastic system
covariance `Q̂⁻¹Ω̂₀Q̂⁻¹`. -/
theorem systemHomoskedasticCovariance_tendstoInMeasure_of_moment_convergence
    {X : ℕ → Ω → Matrix m k ℝ} {SigmaHat : ℕ → Ω → Matrix m m ℝ}
    {Q Omega : Matrix k k ℝ}
    (hQ_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ)
    (hOmega_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle
            (fun i : Fin n => X i.val ω) (SigmaHat n ω)) μ)
    (hQ : TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q))
    (hOmega : TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddle
          (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop (fun _ => Omega))
    (hQ_unit : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticCovariance
          (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop (fun _ => systemAsymptoticVariance Q Omega) :=
  systemSandwichCovariance_tendstoInMeasure
    (μ := μ)
    (Qhat := fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
    (Omegahat := fun n ω =>
      systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω))
    hQ_meas hOmega_meas hQ hOmega hQ_unit

omit [DecidableEq m] in
/-- Fixed-covariance WLLN plus CMT route for the homoskedastic system covariance
`Q̂⁻¹Ω̂₀Q̂⁻¹`. -/
theorem systemHomoskedasticCovariance_tendstoInMeasure_of_fixed_wlln
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    (hQ_int : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hQ_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hQ_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ)
    (hOmega_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hOmega_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hOmega_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ)
    (hQ_unit : IsUnit (μ[fun ω => (X 0 ω)ᵀ * X 0 ω]).det) :
    TendstoInMeasure μ
      (fun n ω => systemHomoskedasticCovariance (fun i : Fin n => X i.val ω) Sigma)
      atTop
      (fun _ => systemAsymptoticVariance
        (μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])) :=
  systemHomoskedasticCovariance_tendstoInMeasure_of_moment_convergence
    (μ := μ)
    (X := X) (SigmaHat := fun _ _ => Sigma)
    (Q := μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
    (Omega := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])
    (fun n => systemNormalizedGram_aestronglyMeasurable hQ_int hQ_ident n)
    (fun n => systemHomoskedasticMiddle_fixed_aestronglyMeasurable Sigma
      hOmega_int hOmega_ident n)
    (systemNormalizedGram_tendstoInMeasure hQ_int hQ_indep hQ_ident)
    (systemHomoskedasticMiddle_fixed_tendstoInMeasure Sigma
      hOmega_int hOmega_indep hOmega_ident)
    hQ_unit

omit [DecidableEq m] in
/-- Estimated-covariance homoskedastic covariance route for Hansen Theorems
11.3 and 11.6.

This combines the fixed-covariance WLLN with a perturbation bound showing that
the estimated covariance middle matrix differs from the fixed-covariance middle
by `o_p(1)`. -/
theorem systemHomoskedasticCovariance_tendstoInMeasure_of_feasible_wlln_substitution
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    {SigmaHat : ℕ → Ω → Matrix m m ℝ}
    (hQ_int : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hQ_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hQ_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ)
    (hOmega_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hOmega_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hOmega_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ)
    (hOmega_hat_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω)) μ)
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω) -
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => 0))
    (hQ_unit : IsUnit (μ[fun ω => (X 0 ω)ᵀ * X 0 ω]).det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticCovariance (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop
      (fun _ => systemAsymptoticVariance
        (μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])) := by
  have hQ :
      TendstoInMeasure μ
        (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
        atTop (fun _ => μ[fun ω => (X 0 ω)ᵀ * X 0 ω]) :=
    systemNormalizedGram_tendstoInMeasure hQ_int hQ_indep hQ_ident
  have hOmegaFixed :
      TendstoInMeasure μ
        (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
        atTop (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
    systemHomoskedasticMiddle_fixed_tendstoInMeasure Sigma
      hOmega_int hOmega_indep hOmega_ident
  have hOmegaHat :
      TendstoInMeasure μ
        (fun n ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω))
        atTop (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
    systemHomoskedasticMiddle_feasible_tendstoInMeasure_of_substitution hOmegaFixed hsub
  exact systemHomoskedasticCovariance_tendstoInMeasure_of_moment_convergence
    (μ := μ)
    (X := X) (SigmaHat := SigmaHat)
    (Q := μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
    (Omega := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])
    (fun n => systemNormalizedGram_aestronglyMeasurable hQ_int hQ_ident n)
    hOmega_hat_meas hQ hOmegaHat hQ_unit

/-- **Stacked-scalar support for Hansen Theorem 11.3.**

For the stacked system, the Chapter 7 HC0 and homoskedastic Star covariance
consistency results apply directly to the system least-squares design. This
theorem assembles those convergence and measurability results into Chapter 8's
covariance-estimator interface, restating the HC0 limit with the Chapter 11
`systemAsymptoticVariance` notation. Hansen's displayed multivariate system
middle matrices are exposed separately by `systemRobustMiddle` and
`systemRobustCovariance`. -/
theorem systemCovariance_consistent_of_iidRobustFeasibleHCMomentConditions
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (hm : IidRobustFeasibleHCMomentConditions μ X e y β) :
    CovarianceEstimatorConsistent μ
        (fun n ω =>
          olsHetCovStar (stackRegressors X n ω) (stackOutcomes y n ω))
        (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)) ∧
      CovarianceEstimatorConsistent μ
        (fun n ω =>
          olsHomoCovStar (stackRegressors X n ω) (stackOutcomes y n ω))
        (homoAsymCov μ X e) := by
  constructor
  · refine covarianceEstimatorConsistent_of_tendstoInMeasure _ _ ?hV_meas ?hV
    · exact olsHetCovStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toRobustCovarianceConsistencyConditions.toSampleMomentAssumption71
        β hm.model hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable
    · simpa [systemAsymptoticVariance, heteroAsymCov] using
        olsHetCovStar_tendstoInMeasure_of_iidRobustFeasibleHCMomentConditions
          (μ := μ) (X := X) (e := e) (y := y) β hm
  · refine covarianceEstimatorConsistent_of_tendstoInMeasure _ _ ?hV0_meas ?hV0
    · exact olsHomoskedasticCovStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toErrorVarianceConsistencyConditions.toSampleMomentAssumption71
        β hm.model hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable
    · exact olsHomoCovStar_tendstoInMeasure_of_iidRobustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β hm

omit [IsProbabilityMeasure μ] [DecidableEq q] in
/-- Covariance consistency for smooth functions of system coefficients. -/
theorem systemDeltaCovariance_consistent
    (Vθhat : ℕ → Ω → Matrix q q ℝ) (Vθ : Matrix q q ℝ)
    (hVθ : CovarianceEstimatorConsistent μ Vθhat Vθ) :
    CovarianceEstimatorConsistent μ Vθhat Vθ :=
  hVθ

end HansenEconometrics
