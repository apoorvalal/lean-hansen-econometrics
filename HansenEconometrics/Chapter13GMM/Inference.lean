import HansenEconometrics.Chapter13GMM.Asymptotics
import HansenEconometrics.AsymptoticUtils.DeltaMethod
import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter9HypothesisTesting

/-!
# Chapter 13 — GMM restrictions and inference

This module contains Hansen Theorems 13.8--13.11. It keeps the Chapter 13
surface small by reusing two earlier layers:

* Chapter 8 minimum-distance estimators and constrained-estimator limits;
* Chapter 9 Wald quadratic-form and chi-square results.

The only new deterministic objects are the normalized sample GMM Gram and
thin GMM names for the constrained estimators and their covariances.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory
  ProbabilityTheory ENNReal

namespace HansenEconometrics

@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    {i j : Type*} [Fintype i] [Fintype j] :
    MeasurableSpace (Matrix i j ℝ) :=
  matrixBorelMeasurableSpace i j

private lemma matrixBorelSpaceInst
    {i j : Type*} [Fintype i] [Fintype j] :
    @BorelSpace (Matrix i j ℝ) _
      (matrixBorelMeasurableSpaceInst (i := i) (j := j)) :=
  matrixBorelSpace i j

attribute [local instance] matrixBorelMeasurableSpaceInst matrixBorelSpaceInst

variable {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
variable {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
variable {k l q : Type*}
variable [Fintype k] [Fintype l] [Fintype q]
variable [DecidableEq k] [DecidableEq l] [DecidableEq q]

/-! ## Wald inference -/

/-- Hansen's GMM Wald statistic, expressed through Chapter 9's canonical
restriction quadratic form. The first input is the scaled restriction gap. -/
noncomputable def gmmWaldStatOrZero
    {r : ℕ} (gap : Fin r → ℝ)
    (VthetaHat : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  restrictionWaldStatOrZero gap VthetaHat

omit [Fintype l] [Fintype q] [DecidableEq l] [DecidableEq q] in
/-- Delta-method bridge for GMM restriction gaps. It turns a coefficient
Gaussian limit and the Assumption 7.3 first-order remainder into the Gaussian
limit used by the Wald theorem. -/
theorem gmmRestrictionGap_tendstoInDistribution
    {r : ℕ}
    (T : ℕ → OmegaSpace → k → ℝ)
    (gap : ℕ → OmegaSpace → Fin r → ℝ)
    (Rderiv : Matrix k (Fin r) ℝ) (V : Matrix k k ℝ)
    (hV : V.PosSemidef)
    (hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V))
    (hgap_meas : ∀ n, AEMeasurable
      (fun omega =>
        (WithLp.toLp 2 (gap n omega) : EuclideanSpace ℝ (Fin r))) mu)
    (hrem : TendstoInMeasure mu
      (fun n omega =>
        (WithLp.toLp 2 (gap n omega) : EuclideanSpace ℝ (Fin r)) -
          matrixContinuousLinearMap Rderivᵀ
            (WithLp.toLp 2 (T n omega)))
      atTop (fun _ => 0)) :
    TendstoInDistribution gap atTop
      (fun z : EuclideanSpace ℝ (Fin r) => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 (Rderivᵀ * V * Rderiv)) := by
  let Te : ℕ → OmegaSpace → EuclideanSpace ℝ k := fun n omega =>
    WithLp.toLp 2 (T n omega)
  let Ge : ℕ → OmegaSpace → EuclideanSpace ℝ (Fin r) := fun n omega =>
    WithLp.toLp 2 (gap n omega)
  have hTe : TendstoInDistribution Te atTop
      (fun z : EuclideanSpace ℝ k => z) (fun _ => mu)
      (multivariateGaussian 0 V) := by
    have hmap := hT.continuous_comp
      (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [Te, Function.comp_def] using hmap
  have hGe : TendstoInDistribution Ge atTop
      (fun z : EuclideanSpace ℝ (Fin r) => z) (fun _ => mu)
      (multivariateGaussian 0 (Rderivᵀ * V * Rderiv)) := by
    simpa [Ge, Te] using
      smoothFunction_asymptoticNormality_gaussian
        (S := V) (R := Rderivᵀ) hV hTe hrem hgap_meas
  have hout := hGe.continuous_comp
    (PiLp.continuous_ofLp 2 (fun _ : Fin r => ℝ))
  simpa [Ge, Function.comp_def] using hout

omit [Fintype q] [DecidableEq q] in
-- The proof composes the Chapter 13 coefficient CLT, Chapter 6 delta method,
-- and Chapter 9 Wald quadratic-form theorem.
/-- **Hansen Theorem 13.8.** Under Assumption 12.2, the Assumption 7.3
restriction linearization, and the null, the GMM Wald statistic converges to
`chiSquared r`. -/
theorem gmmWaldStatOrZero_tendstoInDistribution_of_assumption12_2
    {r : ℕ} [Fact (0 < r)]
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e)
    (W : Matrix l l ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu)
    (hWhat_tendsto : TendstoInMeasure mu What atTop (fun _ => W))
    (hW : W.PosDef)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega)
    (rfun : (k → ℝ) → (Fin r → ℝ)) (theta0 : Fin r → ℝ)
    (Rderiv : Matrix k (Fin r) ℝ)
    (hnull : rfun b = theta0)
    (hbeta_meas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b)) mu)
    (hgap_meas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        (WithLp.toLp 2
          (Real.sqrt (n : ℝ) •
            (rfun (gmmBetaOrZero
              (stackRegressors X n omega) (stackRegressors Z n omega)
              (stackOutcomes Y n omega) (What n omega)) - rfun b)) :
          EuclideanSpace ℝ (Fin r))) mu)
    (hrem : TendstoInMeasure mu
      (fun (n : ℕ) omega =>
        (WithLp.toLp 2
          (Real.sqrt (n : ℝ) •
            (rfun (gmmBetaOrZero
              (stackRegressors X n omega) (stackRegressors Z n omega)
              (stackOutcomes Y n omega) (What n omega)) - rfun b)) :
          EuclideanSpace ℝ (Fin r)) -
          matrixContinuousLinearMap Rderivᵀ
            (WithLp.toLp 2
              (Real.sqrt (n : ℝ) •
                (gmmBetaOrZero
                  (stackRegressors X n omega) (stackRegressors Z n omega)
                  (stackOutcomes Y n omega) (What n omega) - b))))
      atTop (fun _ => 0))
    {VthetaHat : ℕ → OmegaSpace → Matrix (Fin r) (Fin r) ℝ}
    (hVtheta_meas : ∀ n, AEStronglyMeasurable (VthetaHat n) mu)
    (hVtheta : TendstoInMeasure mu VthetaHat atTop
      (fun _ => Rderivᵀ *
        gmmAsymptoticVarianceStar
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          W (scoreCovMat mu Z e) * Rderiv))
    (hVtheta_posDef :
      (Rderivᵀ *
        gmmAsymptoticVarianceStar
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          W (scoreCovMat mu Z e) * Rderiv).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        gmmWaldStatOrZero
          (Real.sqrt (n : ℝ) •
            (rfun (gmmBetaOrZero
              (stackRegressors X n omega) (stackRegressors Z n omega)
              (stackOutcomes Y n omega) (What n omega)) - theta0))
          (VthetaHat n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared r) := by
  let V : Matrix k k ℝ :=
    gmmAsymptoticVarianceStar
      (twoSLSCombinedQZX
        (popGram mu (twoSLSCombinedRegressors Z X)))
      W (scoreCovMat mu Z e)
  let T : ℕ → OmegaSpace → k → ℝ := fun n omega =>
    Real.sqrt (n : ℝ) •
      (gmmBetaOrZero
        (stackRegressors X n omega) (stackRegressors Z n omega)
        (stackOutcomes Y n omega) (What n omega) - b)
  let gap : ℕ → OmegaSpace → Fin r → ℝ := fun n omega =>
    Real.sqrt (n : ℝ) •
      (rfun (gmmBetaOrZero
        (stackRegressors X n omega) (stackRegressors Z n omega)
        (stackOutcomes Y n omega) (What n omega)) - theta0)
  have hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V) := by
    simpa [T, V] using
      gmmBetaOrZero_tendstoInDistribution_of_assumption12_2
        h W hWhat_meas hWhat_tendsto hW b hmodel hbeta_meas
  have hV : V.PosSemidef := by
    exact gmmAsymptoticVarianceStar_posSemidef _ W (scoreCovMat mu Z e)
      (scoreCovMat_posSemidef (μ := mu) (X := Z) (e := e) h.score_clt)
  have hgap : TendstoInDistribution gap atTop
      (fun z : EuclideanSpace ℝ (Fin r) => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 (Rderivᵀ * V * Rderiv)) := by
    exact gmmRestrictionGap_tendstoInDistribution
      T gap Rderiv V hV hT (by simpa [gap, hnull] using hgap_meas)
        (by simpa [gap, T, hnull] using hrem)
  have hLaw : HasLaw
      (fun z : EuclideanSpace ℝ (Fin r) => z)
      (multivariateGaussian 0 (Rderivᵀ * V * Rderiv))
      (multivariateGaussian 0 (Rderivᵀ * V * Rderiv)) := by
    simpa [id] using
      (HasLaw.id (μ := multivariateGaussian 0 (Rderivᵀ * V * Rderiv)))
  have hwald :=
    restrictionWaldStatOrZero_tendstoInDistribution_chiSquared
      (μ := mu) (ν := multivariateGaussian 0 (Rderivᵀ * V * Rderiv))
      (T := gap) (Z := fun z : EuclideanSpace ℝ (Fin r) => z)
      (VthetaHat := VthetaHat) (Vtheta := Rderivᵀ * V * Rderiv)
      hgap hLaw hVtheta_meas (by simpa [V] using hVtheta)
      (by simpa [V] using hVtheta_posDef)
  simpa [gmmWaldStatOrZero, gap] using hwald

omit [Fintype q] [DecidableEq q] in
/-- Size form of Hansen Theorem 13.8. A chi-square critical value with upper
tail mass `alpha` gives asymptotic rejection probability `alpha`. -/
theorem gmmWaldTest_rejectionProb_tendsto_alpha
    {r : ℕ} [Fact (0 < r)]
    {Wald : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha)
    (hWald : TendstoInDistribution Wald atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared r)) :
    Tendsto (fun n => mu {omega | crit < Wald n omega}) atTop
      (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hWald

/-! ## Linear constrained GMM -/

/-- Normalized sample GMM Gram `Qhat' What Qhat`, where
`Qhat = n⁻¹ Z'X`. This is the random minimum-distance weight in Hansen
equation (13.16). -/
noncomputable def gmmNormalizedGram
    {n : Type*} [Fintype n]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (W : Matrix l l ℝ) :
    Matrix k k ℝ :=
  gmmPopulationGram (sampleQZX Z X) W

/-- Hansen equation (13.16), in totalized form. The normalization in
`gmmNormalizedGram` does not affect the minimum-distance correction. -/
noncomputable def gmmConstrainedBetaStar
    {n : Type*} [Fintype n]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (R : Matrix k q ℝ) (c : q → ℝ) : k → ℝ :=
  mdBetaStar (gmmNormalizedGram X Z W) R c
    (gmmBetaOrZero X Z y W)

/-- Hansen equation (13.18), in compact minimum-distance form. -/
noncomputable def gmmConstrainedAsymptoticVariance
    (Q : Matrix l k ℝ) (W Omega : Matrix l l ℝ)
    (R : Matrix k q ℝ) : Matrix k k ℝ :=
  mdAsymptoticVariance (gmmPopulationGram Q W) R
    (gmmAsymptoticVarianceStar Q W Omega)

omit [DecidableEq l] in
/-- Hansen equation (13.18), expanded into its four textbook terms. -/
theorem gmmConstrainedAsymptoticVariance_eq_hansen_1318
    (Q : Matrix l k ℝ) (W Omega : Matrix l l ℝ)
    (R : Matrix k q ℝ)
    (hGram : (gmmPopulationGram Q W)ᵀ = gmmPopulationGram Q W) :
    gmmConstrainedAsymptoticVariance Q W Omega R =
      gmmAsymptoticVarianceStar Q W Omega
        - (gmmPopulationGram Q W)⁻¹ * R *
            (Rᵀ * (gmmPopulationGram Q W)⁻¹ * R)⁻¹ * Rᵀ *
            gmmAsymptoticVarianceStar Q W Omega
        - gmmAsymptoticVarianceStar Q W Omega * R *
            (Rᵀ * (gmmPopulationGram Q W)⁻¹ * R)⁻¹ * Rᵀ *
            (gmmPopulationGram Q W)⁻¹
        + (gmmPopulationGram Q W)⁻¹ * R *
            (Rᵀ * (gmmPopulationGram Q W)⁻¹ * R)⁻¹ * Rᵀ *
            gmmAsymptoticVarianceStar Q W Omega * R *
            (Rᵀ * (gmmPopulationGram Q W)⁻¹ * R)⁻¹ * Rᵀ *
            (gmmPopulationGram Q W)⁻¹ := by
  exact mdAsymptoticVariance_eq_hansen_expanded
    (gmmPopulationGram Q W) R (gmmAsymptoticVarianceStar Q W Omega) hGram

set_option maxHeartbeats 1200000 in
-- The proof composes the Chapter 13 GMM CLT with Chapter 8 random-weight MD.
/-- **Hansen Theorem 13.9.** Under Assumption 12.2, a linear constrained
GMM estimator has the minimum-distance Gaussian limit in equation (13.18). -/
theorem gmmConstrainedBetaStar_tendstoInDistribution_of_assumption12_2
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e)
    (W : Matrix l l ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu)
    (hWhat_tendsto : TendstoInMeasure mu What atTop (fun _ => W))
    (hW : W.PosDef)
    (R : Matrix k q ℝ) (c : q → ℝ)
    (hR : Function.Injective R.mulVec)
    (b : k → ℝ)
    (hrestrict : Rᵀ *ᵥ b = c)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega)
    (hmeas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b)) mu) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmConstrainedBetaStar
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) R c - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmConstrainedAsymptoticVariance
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          W (scoreCovMat mu Z e) R)) := by
  let Q : Matrix l k ℝ :=
    twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))
  let V : Matrix k k ℝ := gmmAsymptoticVarianceStar Q W (scoreCovMat mu Z e)
  let bhat : ℕ → OmegaSpace → k → ℝ := fun n omega =>
    gmmBetaOrZero
      (stackRegressors X n omega) (stackRegressors Z n omega)
      (stackOutcomes Y n omega) (What n omega)
  let Ghat : ℕ → OmegaSpace → Matrix k k ℝ := fun n omega =>
    gmmNormalizedGram
      (stackRegressors X n omega) (stackRegressors Z n omega)
      (What n omega)
  let G : Matrix k k ℝ := gmmPopulationGram Q W
  have hMoment := h.toGMMMomentCLTConditions
    What W hWhat_meas hWhat_tendsto hW
  have hBeta : TendstoInDistribution
      (fun (n : ℕ) omega => Real.sqrt (n : ℝ) • (bhat n omega - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V) := by
    simpa [Q, V, bhat] using
      gmmBetaOrZero_tendstoInDistribution_of_assumption12_2
        h W hWhat_meas hWhat_tendsto hW b hmodel hmeas
  have hGhat_meas : ∀ n, AEStronglyMeasurable (Ghat n) mu := by
    intro n
    exact gmmPopulationGram_aestronglyMeasurable
      _ _ (hMoment.q_meas n) (hWhat_meas n)
  have hGhat : TendstoInMeasure mu Ghat atTop (fun _ => G) := by
    simpa [Ghat, G, Q, gmmNormalizedGram] using
      gmmPopulationGram_tendstoInMeasure
        hMoment.toGMMWeightConvergenceConditions
  have hG : G.PosDef := by
    exact LinearGMM.gram_posDef Q W hW h.qzx_rank
  have hV : V.PosSemidef := by
    exact gmmAsymptoticVarianceStar_posSemidef Q W (scoreCovMat mu Z e)
      (scoreCovMat_posSemidef (μ := mu) (X := Z) (e := e) h.score_clt)
  have hmd :=
    mdBeta_randomWeight_tendstoInDistribution_multivariateGaussian_of_posDef
      (fun n => Real.sqrt (n : ℝ)) bhat Ghat G R c b V hV
      hGhat_meas hGhat hG hR hrestrict hBeta
  simpa [gmmConstrainedBetaStar, gmmConstrainedAsymptoticVariance,
    gmmNormalizedGram, mdScaledError, bhat, Ghat, G, Q, V] using hmd

/-! ## Efficient constrained GMM -/

/-- Hansen equation (13.19), exposed as the Chapter 8 efficient
minimum-distance estimator. -/
noncomputable def gmmEfficientConstrainedBetaStar
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ)
    (bhat : k → ℝ) : k → ℝ :=
  emdBetaStar R c V bhat

/-- Hansen equation (13.20), the efficient constrained GMM covariance. -/
noncomputable def gmmEfficientConstrainedAsymptoticVariance
    (R : Matrix k q ℝ) (V : Matrix k k ℝ) : Matrix k k ℝ :=
  emdAsymptoticVariance R V

omit [DecidableEq k] in
/-- Hansen equation (13.20), in its displayed covariance form. -/
theorem gmmEfficientConstrainedAsymptoticVariance_eq_hansen_1320
    (R : Matrix k q ℝ) (V : Matrix k k ℝ) :
    gmmEfficientConstrainedAsymptoticVariance R V =
      V - V * R * (Rᵀ * V * R)⁻¹ * Rᵀ * V :=
  emdAsymptoticVariance_eq_hansen_826 R V

set_option maxHeartbeats 1200000 in
-- Matrix inversion CMT and the Chapter 8 random-weight MD theorem are costly.
/-- **Hansen Theorem 13.10.** A consistent estimate of the unrestricted
efficient-GMM covariance gives the efficient constrained Gaussian limit. -/
theorem gmmEfficientConstrainedBetaStar_tendstoInDistribution
    (root : ℕ → ℝ)
    (bhat : ℕ → OmegaSpace → k → ℝ)
    (Vhat : ℕ → OmegaSpace → Matrix k k ℝ)
    (V : Matrix k k ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (b : k → ℝ)
    (hVhat_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu)
    (hVhat : TendstoInMeasure mu Vhat atTop (fun _ => V))
    (hV : V.PosDef)
    (hR : Function.Injective R.mulVec)
    (hrestrict : Rᵀ *ᵥ b = c)
    (hBeta : TendstoInDistribution
      (fun n omega => root n • (bhat n omega - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V)) :
    TendstoInDistribution
      (fun n omega => root n •
        (gmmEfficientConstrainedBetaStar R c (Vhat n omega)
          (bhat n omega) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmEfficientConstrainedAsymptoticVariance R V)) := by
  let What : ℕ → OmegaSpace → Matrix k k ℝ :=
    fun n omega => (Vhat n omega)⁻¹
  have hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hVhat_meas n)
  have hWhat : TendstoInMeasure mu What atTop (fun _ => V⁻¹) := by
    exact tendstoInMeasure_matrix_inv hVhat_meas hVhat
      (fun _ => (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit)
  have hmd :=
    mdBeta_randomWeight_tendstoInDistribution_multivariateGaussian_of_posDef
      root bhat What V⁻¹ R c b V hV.posSemidef hWhat_meas hWhat
      hV.inv hR hrestrict hBeta
  have hVunit : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit
  have hGram : IsUnit (Rᵀ * V * R).det :=
    restrictionCov_det_isUnit_of_cov_posDef V R hV hR
  rw [mdAsymptoticVariance_efficientWeight_eq_emd
    R V hVunit hV.isHermitian.eq hGram] at hmd
  simpa [gmmEfficientConstrainedBetaStar,
    gmmEfficientConstrainedAsymptoticVariance, emdBetaStar,
    mdScaledError, What] using hmd

/-! ## Nonlinear constrained GMM -/

/-- **Hansen Theorem 13.11.** A nonlinear constrained GMM estimator has the
same first-order minimum-distance limit once Assumption 8.3 supplies its
linearization. -/
theorem gmmNonlinearConstrainedBeta_tendstoInDistribution
    (root : ℕ → ℝ) (btilde : ℕ → OmegaSpace → k → ℝ) (b : k → ℝ)
    (G : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (T : ℕ → OmegaSpace → k → ℝ) (V : Matrix k k ℝ)
    (hV : V.PosSemidef)
    (hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V))
    (hlinear : ConstrainedEstimatorLinearization
      mu root btilde b G Rderiv T) :
    TendstoInDistribution (constrainedScaledError root btilde b) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 (mdAsymptoticVariance G Rderiv V)) :=
  nonlinearConstrainedEstimator_tendstoInDistribution_multivariateGaussian
    root btilde b G Rderiv T V hV hT hlinear

/-- Efficient specialization of Hansen Theorem 13.11, with covariance
`V - V R (R' V R)⁻¹ R' V`. -/
theorem gmmNonlinearEfficientConstrainedBeta_tendstoInDistribution
    (root : ℕ → ℝ) (btilde : ℕ → OmegaSpace → k → ℝ) (b : k → ℝ)
    (Rderiv : Matrix k q ℝ)
    (T : ℕ → OmegaSpace → k → ℝ) (V : Matrix k k ℝ)
    (hV : V.PosDef)
    (hR : Function.Injective Rderiv.mulVec)
    (hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V))
    (hlinear : ConstrainedEstimatorLinearization
      mu root btilde b V⁻¹ Rderiv T) :
    TendstoInDistribution (constrainedScaledError root btilde b) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmEfficientConstrainedAsymptoticVariance Rderiv V)) := by
  have hraw := gmmNonlinearConstrainedBeta_tendstoInDistribution
    root btilde b V⁻¹ Rderiv T V hV.posSemidef hT hlinear
  have hVunit : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit
  have hGram : IsUnit (Rderivᵀ * V * Rderiv).det :=
    restrictionCov_det_isUnit_of_cov_posDef V Rderiv hV hR
  rw [mdAsymptoticVariance_efficientWeight_eq_emd
    Rderiv V hVunit hV.isHermitian.eq hGram] at hraw
  exact hraw

end HansenEconometrics
