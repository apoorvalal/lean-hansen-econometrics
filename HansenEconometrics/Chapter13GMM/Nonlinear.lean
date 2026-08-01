import HansenEconometrics.Chapter13GMM
import HansenEconometrics.AsymptoticUtils.DeltaMethod

/-!
# Chapter 13 — nonlinear GMM

This module proves Hansen Proposition 13.1. The omitted regularity conditions
are stated as two reusable premises: a Gaussian limit for the scaled sample
moment and an `o_p(1)` first-order remainder for the nonlinear estimator.

The proof uses the generic GMM influence matrix from
`Chapter13GMM.Primitives` and the Chapter 6 Gaussian delta-method theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Function Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
variable {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
variable {k l : Type*}
variable [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

/-- **Hansen Proposition 13.1.** A nonlinear GMM estimator with the standard
first-order expansion has the sandwich Gaussian limit.

Here `Q` is the derivative of the population moment. Therefore, the
linearization uses the negative GMM influence matrix. Its sign cancels from
the covariance. -/
theorem nonlinearGMMBeta_tendstoInDistribution
    (bhat : ℕ → OmegaSpace → k → ℝ) (b : k → ℝ)
    (score : ℕ → OmegaSpace → l → ℝ)
    (Q : Matrix l k ℝ) (W Omega : Matrix l l ℝ)
    (hOmega : Omega.PosSemidef)
    (hscore : TendstoInDistribution score atTop
      (fun z : EuclideanSpace ℝ l => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 Omega))
    (hbeta_meas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        (WithLp.toLp 2
          (Real.sqrt (n : ℝ) • (bhat n omega - b)) :
          EuclideanSpace ℝ k)) mu)
    (hrem : TendstoInMeasure mu
      (fun (n : ℕ) omega =>
        (WithLp.toLp 2
          (Real.sqrt (n : ℝ) • (bhat n omega - b)) :
          EuclideanSpace ℝ k) -
          matrixContinuousLinearMap
            (-LinearGMM.influenceMatrixStar Q W)
            (WithLp.toLp 2 (score n omega)))
      atTop (fun _ => 0)) :
    TendstoInDistribution
      (fun (n : ℕ) omega => Real.sqrt (n : ℝ) • (bhat n omega - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmAsymptoticVarianceStar Q W Omega)) := by
  let T : ℕ → OmegaSpace → EuclideanSpace ℝ l := fun n omega =>
    WithLp.toLp 2 (score n omega)
  let Y : ℕ → OmegaSpace → EuclideanSpace ℝ k := fun n omega =>
    WithLp.toLp 2 (Real.sqrt (n : ℝ) • (bhat n omega - b))
  let A : Matrix k l ℝ := -LinearGMM.influenceMatrixStar Q W
  have hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ l => z) (fun _ => mu)
      (multivariateGaussian 0 Omega) := by
    have hmap := hscore.continuous_comp
      (PiLp.continuous_toLp 2 (fun _ : l => ℝ))
    simpa [T, Function.comp_def] using hmap
  have hY : TendstoInDistribution Y atTop
      (fun z : EuclideanSpace ℝ k => z) (fun _ => mu)
      (multivariateGaussian 0 (A * Omega * Aᵀ)) := by
    exact smoothFunction_asymptoticNormality_gaussian
      (S := Omega) (R := A) hOmega hT
      (by simpa [Y, T, A] using hrem)
      (by simpa [Y] using hbeta_meas)
  have hcov : A * Omega * Aᵀ =
      gmmAsymptoticVarianceStar Q W Omega := by
    simp [A, gmmAsymptoticVarianceStar,
      LinearGMM.asymptoticVarianceStar]
    exact neg_neg _
  rw [hcov] at hY
  have hout := hY.continuous_comp
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  simpa [Y, Function.comp_def] using hout

/-- Efficient-weight form of Hansen Proposition 13.1. With a positive-definite
moment covariance and a full-rank derivative, the sandwich covariance reduces
to `(Q' Omega⁻¹ Q)⁻¹`. -/
theorem nonlinearGMMBeta_tendstoInDistribution_efficient
    (bhat : ℕ → OmegaSpace → k → ℝ) (b : k → ℝ)
    (score : ℕ → OmegaSpace → l → ℝ)
    (Q : Matrix l k ℝ) (Omega : Matrix l l ℝ)
    (hOmega : Omega.PosDef) (hQ : Function.Injective Q.mulVec)
    (hscore : TendstoInDistribution score atTop
      (fun z : EuclideanSpace ℝ l => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 Omega))
    (hbeta_meas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        (WithLp.toLp 2
          (Real.sqrt (n : ℝ) • (bhat n omega - b)) :
          EuclideanSpace ℝ k)) mu)
    (hrem : TendstoInMeasure mu
      (fun (n : ℕ) omega =>
        (WithLp.toLp 2
          (Real.sqrt (n : ℝ) • (bhat n omega - b)) :
          EuclideanSpace ℝ k) -
          matrixContinuousLinearMap
            (-LinearGMM.influenceMatrixStar Q Omega⁻¹)
            (WithLp.toLp 2 (score n omega)))
      atTop (fun _ => 0)) :
    TendstoInDistribution
      (fun (n : ℕ) omega => Real.sqrt (n : ℝ) • (bhat n omega - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmPopulationGram Q Omega⁻¹)⁻¹) := by
  have hgeneral := nonlinearGMMBeta_tendstoInDistribution
    bhat b score Q Omega⁻¹ Omega hOmega.posSemidef
    hscore hbeta_meas hrem
  rw [gmmAsymptoticVarianceStar_efficient Q Omega hOmega hQ] at hgeneral
  exact hgeneral

end HansenEconometrics
