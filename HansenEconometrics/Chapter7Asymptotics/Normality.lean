import Mathlib.Probability.CentralLimitTheorem
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.StochasticOrder
import HansenEconometrics.Interfaces.Asymptotics
import HansenEconometrics.ProbabilityUtils
import HansenEconometrics.ChiSquared
import HansenEconometrics.Chapter7Asymptotics.Consistency
import HansenEconometrics.Chapter7Asymptotics.SandwichAssembly

/-!
# Chapter 7 Asymptotics: Normality

This file contains the Chapter 7 distributional layer:

* scalar score CLTs and the Cramér-Wold vector score bridge;
* OLS asymptotic-normality wrappers for `olsBetaStar` and `olsBetaOrZero`;
* Gaussian linear-map, Mahalanobis, and chi-square Wald bridge results;
* multivariate Wald packaging for homoskedastic and robust covariance estimators.
-/

open scoped Matrix Real

namespace HansenEconometrics

open Matrix

section Assumption72

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst :
    MeasurableSpace (Matrix k k ℝ) :=
  matrixBorelMeasurableSpace k k

attribute [local instance] matrixBorelMeasurableSpaceInst

omit [DecidableEq k] in
private lemma matrixBorelSpaceInst : BorelSpace (Matrix k k ℝ) :=
  matrixBorelSpace k k

attribute [local instance] matrixBorelSpaceInst

omit [DecidableEq k] in
/-- Move a fixed matrix multiplication from the left side of a dot product to the right side. -/
theorem mulVec_dotProduct_right {q : Type*} [Fintype q]
    (M : Matrix q k ℝ) (v : k → ℝ) (a : q → ℝ) :
    (M *ᵥ v) ⬝ᵥ a = v ⬝ᵥ (Mᵀ *ᵥ a) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]

/-- **Hansen Theorem 7.2, scalar-projection score CLT.**

For every fixed vector `a`, the projected score sum
`(1 / √n) ∑_{i<n} (eᵢXᵢ)·a` converges in distribution to the Gaussian with the
matching scalar variance. This is the one-dimensional CLT supplied by Mathlib,
specialized to the score projections that appear in OLS asymptotic normality.

This is the one-dimensional projection face used by the vector-valued
Cramér-Wold theorem below. -/
theorem scoreProj_sum_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range n, (e i ω • X i ω) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hdot_meas := measurable_dotProduct_right (k := k) a
  have hident_scalar : ∀ i,
      IdentDistrib (fun ω => (e i ω • X i ω) ⬝ᵥ a)
        (fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a) μ μ := by
    intro i
    simpa [Function.comp_def] using h.ident_cross i |>.comp hdot_meas
  have hindep_scalar :
      iIndepFun (fun i ω => (e i ω • X i ω) ⬝ᵥ a) μ := by
    simpa [Function.comp_def] using
      h.iIndep_cross.comp (fun _ v => v ⬝ᵥ a) (fun _ => hdot_meas)
  have hmean := scoreProj_integral_zero (μ := μ)
    (X := X) (e := e) h.toSampleMomentAssumption71 a
  have hmean_integral :
      (∫ ω, (e 0 ω • X 0 ω) ⬝ᵥ a ∂μ) = 0 := by
    simpa using hmean
  have hclt := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := μ) (P' := ν) (X := fun i ω => (e i ω • X i ω) ⬝ᵥ a)
    (Y := Z) hZ (h.memLp_cross_projection a) hindep_scalar hident_scalar
  convert hclt using 2 with n ω
  funext ω
  rw [hmean_integral]
  ring

/-- **Hansen Theorem 7.2 in sample-score notation, scalar-projection form.**

This is the same CLT as `scoreProj_sum_tendstoInDistribution_gaussian`,
rewritten in Hansen's notation as `√n · ĝₙ(e)` where
`ĝₙ(e) = n⁻¹∑ eᵢXᵢ`.

The vector-valued CLT below packages these scalar projections through the
reusable Cramér-Wold bridge. -/
theorem scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hsum := scoreProj_sum_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ
  convert hsum using 2 with n
  funext ω
  rw [sqrt_smul_sampleCrossMoment_stack_eq_inv_sqrt_sum]
  simp [sum_dotProduct, smul_eq_mul]

/-- **Hansen Theorem 7.2, scalar-projection score CLT with `Ω`.**

This is `scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian`
with the Gaussian variance rewritten as the quadratic form
`a' Ω a`, where `Ω = scoreCovMat μ X e`. -/
theorem scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian_cov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (a ⬝ᵥ (scoreCovMat μ X e *ᵥ a)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hZ' : HasLaw Z
      (gaussianReal 0 (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal) ν := by
    rw [scoreProj_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h a]
    exact hZ
  exact scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ'

/-- **Hansen Theorem 7.2, all scalar projections with `Ω`.**

This packages the scalar projection family used by the vector-valued
Cramér-Wold theorem below: for every fixed direction `a`, the scalar projection
of `√n · ĝₙ(e)` has Gaussian limit with variance `a' Ω a`. -/
theorem scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian_cov_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (a ⬝ᵥ (scoreCovMat μ X e *ᵥ a)).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian_cov
      (μ := μ) (ν := ν) (X := X) (e := e) h a (hZ a)

/-- **Hansen Theorem 7.2, vector score CLT in Euclidean-space form.**

The scaled sample score `√n · ĝₙ(e)`, coerced to `EuclideanSpace`, converges to
the centered multivariate Gaussian with covariance matrix `Ω`. The proof uses
the reusable Cramér-Wold bridge plus the scalar projection CLTs above. -/
theorem scoreEuclidean_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        WithLp.toLp 2
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 (scoreCovMat μ X e)) := by
  refine cramerWold_tendstoInDistribution ?_ (by fun_prop) ?_
  · intro n
    exact (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).measurable.comp_aemeasurable
      ((sampleCrossMoment_stack_aestronglyMeasurable
        (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71 n).const_smul
          (Real.sqrt (n : ℝ))).aemeasurable
  · intro t
    let a : k → ℝ := t.ofLp
    have hLawDot := hasLaw_multivariateGaussian_zero_dotProduct
      (S := scoreCovMat μ X e)
      (scoreCovMat_posSemidef (μ := μ) (X := X) (e := e) h) a
    have hLawDual : HasLaw
        (fun z : EuclideanSpace ℝ k =>
          (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ k) t) z)
        (gaussianReal 0 (a ⬝ᵥ (scoreCovMat μ X e *ᵥ a)).toNNReal)
        (multivariateGaussian 0 (scoreCovMat μ X e)) := by
      refine hLawDot.congr (ae_of_all _ fun z => ?_)
      change inner ℝ t z = z.ofLp ⬝ᵥ a
      simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k) t.ofLp z.ofLp)
    have hscalar := scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian_cov
      (μ := μ) (ν := multivariateGaussian 0 (scoreCovMat μ X e))
      (X := X) (e := e) h a hLawDual
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hscalar
    intro n
    exact ae_of_all μ (fun ω => by
      change (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a =
        inner ℝ t (WithLp.toLp 2
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
      simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k) t.ofLp
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))).symm)

/-- **Hansen Theorem 7.2, vector score CLT in Chapter 7 function-vector notation.**

This is the public Chapter 7 score CLT: `√n · ĝₙ(e)` converges to the
multivariate Gaussian score vector. The limit random variable is the coordinate
view of the Gaussian on `EuclideanSpace ℝ k`, matching the rest of the chapter's
`k → ℝ` vector notation. -/
theorem scoreVector_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ)
      (multivariateGaussian 0 (scoreCovMat μ X e)) := by
  have hEuclid := scoreEuclidean_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
    (μ := μ) (X := X) (e := e) h.toSampleCLTAssumption72
  have hMap := TendstoInDistribution.continuous_comp
    (g := (WithLp.ofLp : EuclideanSpace ℝ k → k → ℝ))
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)) hEuclid
  simpa [Function.comp_def] using hMap

namespace ScoreCLTConditions

/-- The Chapter 7.2 score proof bundle constructs the stable score-CLT interface. -/
theorem toScoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) :
    ScoreCLT μ
      (fun n ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      (fun z : EuclideanSpace ℝ k => z.ofLp)
      (multivariateGaussian 0 (scoreCovMat μ X e)) where
  score_tendsto := scoreVector_sampleCrossMoment_tendstoInDistribution_multivariateGaussian h

end ScoreCLTConditions

/-- **Hansen Theorem 7.3, feasible leading-score vector Slutsky bridge.**

Conditional on a vector-valued score CLT for `√n · ĝₙ(e)`, the feasible OLS
leading term formed with the random inverse Gram matrix satisfies
`Q̂ₙ⁻¹√nĝₙ(e) ⇒ Q⁻¹Z`. This is the vector version of the inverse-gap step:
the remaining full OLS theorem only has to add the already-negligible
singular-event residual. -/
theorem feasibleScore_tendstoInDistribution_scoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
      atTop
      (fun ω => (popGram μ X)⁻¹ *ᵥ Zscore ω)
      (fun _ => μ) ν := by
  exact matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix
    (μ := μ) (ν := ν)
    (T := fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) •
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
    (Z := Zscore)
    (Ahat := fun n ω => sampleGram (stackRegressors X n ω))
    (A := popGram μ X)
    hScore (fun n => sampleGram_stackRegressors_aestronglyMeasurable h n)
    (sampleGram_stackRegressors_tendstoInMeasure_popGram h) h.Q_nonsing

/-- **Hansen Theorem 7.3, conditional vector OLS Slutsky assembly.**

If the vector score has a distributional limit `Zscore`, then the scaled
totalized OLS estimator has the transformed limit `Q⁻¹Zscore`. The theorem is
conditional only on the vector-valued score CLT; the random inverse and the
singular-event residual are discharged here. -/
theorem olsBetaStar_vector_tendstoInDistribution_scoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop
      (fun ω => (popGram μ X)⁻¹ *ᵥ Zscore ω)
      (fun _ => μ) ν := by
  have hFeasible := feasibleScore_tendstoInDistribution_scoreCLT
    (μ := μ) (ν := ν) (X := X) (e := e) (Zscore := Zscore) h hScore
  have hResidual :=
    sqrt_smul_olsBetaStar_sub_sub_feasScore_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  have hBeta_meas := olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  have hY_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) μ := by
    intro n
    exact (AEStronglyMeasurable.const_smul
      ((hBeta_meas n).sub aestronglyMeasurable_const) (Real.sqrt (n : ℝ))).aemeasurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (n : ℕ) ω =>
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
    (Y := fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
    (Z := fun ω => (popGram μ X)⁻¹ *ᵥ Zscore ω)
    hFeasible hResidual hY_meas

/-- **Hansen Theorem 7.3, ordinary-wrapper conditional vector OLS CLT.**

The same conditional vector asymptotic-normality bridge holds for
`olsBetaOrZero`, the ordinary-OLS wrapper that agrees with `olsBetaStar`
pointwise. -/
theorem olsBetaOrZero_vector_tendstoInDistribution_scoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop
      (fun ω => (popGram μ X)⁻¹ *ᵥ Zscore ω)
      (fun _ => μ) ν := by
  have hstar := olsBetaStar_vector_tendstoInDistribution_scoreCLT
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    (Zscore := Zscore) h β hmodel hScore
  refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hstar
  intro n
  exact ae_of_all μ (fun ω => by
    change
      Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) =
        Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)
    simp)

/-- **Hansen Theorem 7.3, vector asymptotic normality for totalized OLS.**

Under the Chapter 7.2 scalar-projection CLT assumptions, the scaled totalized
OLS estimator converges to the population-inverse transform of the Gaussian
score vector. This theorem discharges the vector score CLT using the
Cramér-Wold score theorem above. -/
theorem olsBetaStar_vector_tendstoInDistribution_multivariateGaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop
      (fun z : EuclideanSpace ℝ k => (popGram μ X)⁻¹ *ᵥ z.ofLp)
      (fun _ => μ)
      (multivariateGaussian 0 (scoreCovMat μ X e)) := by
  exact olsBetaStar_vector_tendstoInDistribution_scoreCLT
    (μ := μ) (ν := multivariateGaussian 0 (scoreCovMat μ X e))
    (X := X) (e := e) (y := y)
    (Zscore := fun z : EuclideanSpace ℝ k => z.ofLp)
    h.toSampleMomentAssumption71 β hmodel
    (scoreVector_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
      (μ := μ) (X := X) (e := e) h)

/-- **Hansen Theorem 7.16/7.3 bridge, totalized estimator.**

The vector OLS CLT implies the scaled coefficient error
`√n(β̂*ₙ - β)` is bounded in probability. This is the coefficient-error factor
needed by the max-residual product-rate proof. -/
theorem sqrt_smul_olsBetaStar_sub_boundedInProbabilityNorm
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    BoundedInProbabilityNorm μ
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) := by
  exact BoundedInProbabilityNorm.of_tendstoInDistribution
    (olsBetaStar_vector_tendstoInDistribution_multivariateGaussian
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)

/-- **Hansen Theorem 7.16, residual uniformity rate.**

Under the score CLT conditions, a correctly specified linear model, and uniform
integrability of squared regressor row norms, the maximum totalized residual
error is `oₚ(1)`.  The proof combines the Chapter 6 root row-norm rate with the
OLS CLT's `√n(β̂*ₙ - β)=Oₚ(1)` factor and the deterministic residual bound. -/
theorem maxResidualErrorStar_tendstoInMeasure_zero_of_uniformIntegrable_rowNorm_sq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hUI : UniformIntegrable (fun i ω => ‖X i ω‖ ^ 2) 1 μ) :
    TendstoInMeasure μ
      (fun n ω => maxResidualErrorStar (stackRegressors X n ω) β (stackErrors e n ω))
      atTop (fun _ => 0) := by
  let rootRow : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt
      ((Fintype.card (Fin n) : ℝ)⁻¹ *
        maxRowNorm (stackRegressors X n ω) ^ 2)
  let betaScaledNorm : ℕ → Ω → ℝ := fun n ω =>
    ‖Real.sqrt (n : ℝ) •
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)‖
  have hRoot : TendstoInMeasure μ rootRow atTop (fun _ => 0) := by
    simpa [rootRow] using
      (sqrt_scaledMaxRowNorm_sq_tendstoInMeasure_zero_of_uniformIntegrable_norm_sq
        (μ := μ) (X := X) hUI)
  have hBetaNorm :=
    sqrt_smul_olsBetaStar_sub_boundedInProbabilityNorm
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hBeta : BoundedInProbability μ betaScaledNorm := by
    intro δ hδ
    obtain ⟨M, hMpos, hMev⟩ := hBetaNorm δ hδ
    refine ⟨M, hMpos, ?_⟩
    filter_upwards [hMev] with n hn
    refine (measure_mono ?_).trans hn
    intro ω hω
    simpa [betaScaledNorm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hω
  have hprod : TendstoInMeasure μ
      (fun n ω => rootRow n ω * betaScaledNorm n ω) atTop (fun _ => 0) :=
    TendstoInMeasure.mul_boundedInProbability hRoot hBeta
  have hboundProduct : TendstoInMeasure μ
      (fun n ω => (Fintype.card k : ℝ) * (rootRow n ω * betaScaledNorm n ω))
      atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) (Fintype.card k : ℝ) hprod
  have hProduct : TendstoInMeasure μ
      (fun n ω =>
        (Fintype.card k : ℝ) * maxRowNorm (stackRegressors X n ω) *
          ‖olsBetaStar
            (stackRegressors X n ω)
            (stackRegressors X n ω *ᵥ β + stackErrors e n ω) - β‖)
      atTop (fun _ => 0) := by
    refine TendstoInMeasure.of_abs_le_zero_real hboundProduct ?_
    intro n ω
    let Xn : Matrix (Fin n) k ℝ := stackRegressors X n ω
    let en : Fin n → ℝ := stackErrors e n ω
    let berr : k → ℝ := olsBetaStar Xn (stackOutcomes y n ω) - β
    have hstack : stackOutcomes y n ω = Xn *ᵥ β + en :=
      stack_linear_model X e y β hmodel n ω
    have hbeta_eq :
        ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖ = ‖berr‖ := by
      simp [berr, Xn, en, ← hstack]
    have hleft_nonneg :
        0 ≤ (Fintype.card k : ℝ) * maxRowNorm Xn *
          ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖ := by
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (norm_nonneg _)
    have hright_nonneg :
        0 ≤ (Fintype.card k : ℝ) * (rootRow n ω * betaScaledNorm n ω) := by
      exact mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    have hscaled :
        (Fintype.card k : ℝ) * maxRowNorm Xn *
            ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖ ≤
          (Fintype.card k : ℝ) * (rootRow n ω * betaScaledNorm n ω) := by
      by_cases hnzero : n = 0
      · have hrow0 : maxRowNorm Xn = 0 := by
          unfold maxRowNorm
          rw [show (fun i : Fin n => ‖Xn i‖) = (0 : Fin n → ℝ) by
            ext i
            subst hnzero
            exact Fin.elim0 i]
          exact norm_zero
        have hleft_zero :
            (Fintype.card k : ℝ) * maxRowNorm Xn *
              ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖ = 0 := by
          simp [hrow0]
        rw [hleft_zero]
        exact hright_nonneg
      · have hrow_eq :
            rootRow n ω * Real.sqrt (n : ℝ) = maxRowNorm (stackRegressors X n ω) := by
          simpa [rootRow] using
            sqrt_scaledMaxRowNorm_sq_mul_sqrt_eq_maxRowNorm (X := X) hnzero ω
        have hrow_eq' :
            maxRowNorm (stackRegressors X n ω) =
              rootRow n ω * Real.sqrt (n : ℝ) :=
          hrow_eq.symm
        have hscaled_beta :
            betaScaledNorm n ω =
              Real.sqrt (n : ℝ) * ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖ := by
          calc
            betaScaledNorm n ω = Real.sqrt (n : ℝ) * ‖berr‖ := by
              change ‖Real.sqrt (n : ℝ) • berr‖ =
                Real.sqrt (n : ℝ) * ‖berr‖
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
            _ = Real.sqrt (n : ℝ) * ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖ := by
              rw [← hbeta_eq]
        have hcore :
            maxRowNorm Xn * ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖ ≤
              rootRow n ω * betaScaledNorm n ω := by
          calc
            maxRowNorm Xn * ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖
                = (rootRow n ω * Real.sqrt (n : ℝ)) *
                    ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖ := by
                    rw [show maxRowNorm Xn = rootRow n ω * Real.sqrt (n : ℝ) by
                      simpa [Xn] using hrow_eq']
            _ = rootRow n ω *
                  (Real.sqrt (n : ℝ) * ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖) := by
                    ring
            _ = rootRow n ω * betaScaledNorm n ω := by rw [← hscaled_beta]
          exact le_rfl
        have hk : 0 ≤ (Fintype.card k : ℝ) := Nat.cast_nonneg _
        calc
          (Fintype.card k : ℝ) * maxRowNorm Xn *
              ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖
              = (Fintype.card k : ℝ) *
                  (maxRowNorm Xn * ‖olsBetaStar Xn (Xn *ᵥ β + en) - β‖) := by
                    ring
          _ ≤ (Fintype.card k : ℝ) * (rootRow n ω * betaScaledNorm n ω) :=
            mul_le_mul_of_nonneg_left hcore hk
    simpa [Xn, en, abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using hscaled
  simpa using
    (scaledMaxResidualErrorStar_tendstoInMeasure_zero_of_scaled_product
      (μ := μ) (X := X) (e := e) β (fun _ => (1 : ℝ))
      (by intro n; norm_num) (by simpa using hProduct))

/-- **Hansen Theorem 7.16, iid finite-row-moment residual uniformity rate.**

If the squared regressor row norms are identically distributed and the first row
has finite second moment, then the Chapter 6 iid UI bridge discharges the row
uniform-integrability assumption in the max-residual rate theorem. -/
theorem maxResidualErrorStar_tendstoInMeasure_zero_of_identDistrib_memLp_rowNorm_sq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hRowMem : MemLp (fun ω => ‖X 0 ω‖ ^ 2) 1 μ)
    (hRowIdent : ∀ i,
      IdentDistrib (fun ω => ‖X i ω‖ ^ 2) (fun ω => ‖X 0 ω‖ ^ 2) μ μ) :
    TendstoInMeasure μ
      (fun n ω => maxResidualErrorStar (stackRegressors X n ω) β (stackErrors e n ω))
      atTop (fun _ => 0) := by
  exact maxResidualErrorStar_tendstoInMeasure_zero_of_uniformIntegrable_rowNorm_sq
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
    (uniformIntegrable_one_of_identDistrib_memLp
      (μ := μ) (Z := fun i ω => ‖X i ω‖ ^ 2) hRowMem hRowIdent)

/-- **Hansen Theorem 7.3, ordinary-wrapper vector asymptotic normality.**

The same non-conditional vector CLT for the textbook-facing `olsBetaOrZero`
wrapper, using the pointwise equality with `olsBetaStar`. -/
theorem olsBetaOrZero_vector_tendstoInDistribution_multivariateGaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop
      (fun z : EuclideanSpace ℝ k => (popGram μ X)⁻¹ *ᵥ z.ofLp)
      (fun _ => μ)
      (multivariateGaussian 0 (scoreCovMat μ X e)) := by
  exact olsBetaOrZero_vector_tendstoInDistribution_scoreCLT
    (μ := μ) (ν := multivariateGaussian 0 (scoreCovMat μ X e))
    (X := X) (e := e) (y := y)
    (Zscore := fun z : EuclideanSpace ℝ k => z.ofLp)
    h.toSampleMomentAssumption71 β hmodel
    (scoreVector_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
      (μ := μ) (X := X) (e := e) h)

/-- **Hansen Theorem 7.3 for literal ordinary OLS under sample-Gram invertibility.**

When every realized stacked sample Gram is invertible, the textbook `olsBeta`
estimator is available pointwise and agrees with `olsBetaOrZero`, so the
ordinary-wrapper vector asymptotic-normality theorem transfers to the dependent
ordinary-OLS surface. -/
theorem olsBeta_vector_tendstoInDistribution_multivariateGaussian_of_invertible
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hInv : ∀ n ω,
      Invertible ((stackRegressors X n ω)ᵀ * stackRegressors X n ω))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          ((letI : Invertible
              ((stackRegressors X n ω)ᵀ * stackRegressors X n ω) := hInv n ω
            olsBeta (stackRegressors X n ω) (stackOutcomes y n ω)) - β))
      atTop
      (fun z : EuclideanSpace ℝ k => (popGram μ X)⁻¹ *ᵥ z.ofLp)
      (fun _ => μ)
      (multivariateGaussian 0 (scoreCovMat μ X e)) := by
  have hOrZero := olsBetaOrZero_vector_tendstoInDistribution_multivariateGaussian
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hOrZero
  intro n
  exact ae_of_all μ (fun ω => by
    letI : Invertible ((stackRegressors X n ω)ᵀ * stackRegressors X n ω) :=
      hInv n ω
    change
      Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β) =
        Real.sqrt (n : ℝ) •
          (olsBeta (stackRegressors X n ω) (stackOutcomes y n ω) - β)
    rw [olsBetaOrZero_eq_olsBeta])

/-- **Hansen Theorem 7.16/7.3 bridge, ordinary-wrapper estimator.**

The ordinary-on-nonsingular wrapper has the same bounded scaled coefficient
error as `olsBetaStar`. -/
theorem sqrt_smul_olsBetaOrZero_sub_boundedInProbabilityNorm
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    BoundedInProbabilityNorm μ
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)) := by
  exact BoundedInProbabilityNorm.of_tendstoInDistribution
    (olsBetaOrZero_vector_tendstoInDistribution_multivariateGaussian
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)

/-- **Hansen Theorem 7.9, nonlinear Delta-method wrapper for totalized OLS.**

This is the Chapter 7-facing nonlinear packaging now that the Chapter 6
Delta-method/law-relabeling layer is available.  If `Yₙ` is the scaled nonlinear
statistic and it differs from the derivative image of
`√n(β̂*ₙ - β)` by `oₚ(1)`, then `Yₙ` has the named Gaussian law of that derivative
image.  Concrete transforms `r(β̂ₙ)` discharge `hrem` from the usual
Fréchet-derivative remainder. -/
theorem nonlinearFunction_olsBetaStar_delta_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q] [DecidableEq q]
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Y : ℕ → Ω → EuclideanSpace ℝ q}
    (hY_meas : ∀ n, AEMeasurable (Y n) μ)
    (hrem :
      TendstoInMeasure μ
        (fun n ω =>
          Y n ω -
            matrixContinuousLinearMap R
              (WithLp.toLp 2
                (Real.sqrt (n : ℝ) •
                  (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))))
        atTop (fun _ => 0))
    (hLimitLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          matrixContinuousLinearMap R
            (WithLp.toLp 2 ((popGram μ X)⁻¹ *ᵥ z.ofLp)))
        (multivariateGaussian 0 (R * heteroAsymCov μ X e * Rᵀ))
        (multivariateGaussian 0 (scoreCovMat μ X e))) :
    TendstoInDistribution Y atTop
      (fun z : EuclideanSpace ℝ q => z)
      (fun _ => μ)
      (multivariateGaussian 0 (R * heteroAsymCov μ X e * Rᵀ)) := by
  let T : ℕ → Ω → EuclideanSpace ℝ k := fun n ω =>
    WithLp.toLp 2
      (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
  have hbeta_raw := olsBetaStar_vector_tendstoInDistribution_multivariateGaussian
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hbeta_euclid :
      TendstoInDistribution T atTop
        (fun z : EuclideanSpace ℝ k =>
          WithLp.toLp 2 ((popGram μ X)⁻¹ *ᵥ z.ofLp))
        (fun _ => μ)
        (multivariateGaussian 0 (scoreCovMat μ X e)) := by
    have hmap := hbeta_raw.continuous_comp
      (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [T, Function.comp_def] using hmap
  have hlin :
      TendstoInDistribution
        (fun n => matrixContinuousLinearMap R ∘ T n)
        atTop
        (matrixContinuousLinearMap R ∘
          fun z : EuclideanSpace ℝ k =>
            WithLp.toLp 2 ((popGram μ X)⁻¹ *ᵥ z.ofLp))
        (fun _ => μ)
        (multivariateGaussian 0 (scoreCovMat μ X e)) :=
    hbeta_euclid.continuous_comp (matrixContinuousLinearMap R).continuous
  have htarget :
      TendstoInDistribution
        (fun n ω => matrixContinuousLinearMap R (T n ω))
        atTop
        (fun z : EuclideanSpace ℝ q => z)
        (fun _ => μ)
        (multivariateGaussian 0 (R * heteroAsymCov μ X e * Rᵀ)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit
        (E := EuclideanSpace ℝ q) hlin hLimitLaw
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => matrixContinuousLinearMap R (T n ω))
    (Y := Y)
    (Z := fun z : EuclideanSpace ℝ q => z)
    htarget hrem hY_meas

/-- **Hansen Theorem 7.9, nonlinear Delta-method wrapper for ordinary OLS.**

Ordinary-wrapper version of
`nonlinearFunction_olsBetaStar_delta_tendstoInDistribution_gaussian`. -/
theorem nonlinearFunction_olsBetaOrZero_delta_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q] [DecidableEq q]
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Y : ℕ → Ω → EuclideanSpace ℝ q}
    (hY_meas : ∀ n, AEMeasurable (Y n) μ)
    (hrem :
      TendstoInMeasure μ
        (fun n ω =>
          Y n ω -
            matrixContinuousLinearMap R
              (WithLp.toLp 2
                (Real.sqrt (n : ℝ) •
                  (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))))
        atTop (fun _ => 0))
    (hLimitLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          matrixContinuousLinearMap R
            (WithLp.toLp 2 ((popGram μ X)⁻¹ *ᵥ z.ofLp)))
        (multivariateGaussian 0 (R * heteroAsymCov μ X e * Rᵀ))
        (multivariateGaussian 0 (scoreCovMat μ X e))) :
    TendstoInDistribution Y atTop
      (fun z : EuclideanSpace ℝ q => z)
      (fun _ => μ)
      (multivariateGaussian 0 (R * heteroAsymCov μ X e * Rᵀ)) := by
  have hrem_star :
      TendstoInMeasure μ
        (fun n ω =>
          Y n ω -
            matrixContinuousLinearMap R
              (WithLp.toLp 2
                (Real.sqrt (n : ℝ) •
                  (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))))
        atTop (fun _ => 0) := by
    simpa using hrem
  exact nonlinearFunction_olsBetaStar_delta_tendstoInDistribution_gaussian
    (μ := μ) (X := X) (e := e) (y := y) h β R hmodel
    hY_meas hrem_star hLimitLaw

/-- **Scaled-score coordinate boundedness from Theorem 7.2.**

Each coordinate of `√n · ĝₙ(e)` is `Oₚ(1)`.  This is the tightness corollary
of the scalar-projection score CLT, using the coordinate basis vector
`Pi.single j 1` and the general fact that real convergence in distribution
implies boundedness in probability. -/
theorem scoreCoordinate_sampleCrossMoment_boundedInProbability
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j : k) :
    BoundedInProbability μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j) := by
  classical
  let a : k → ℝ := Pi.single j 1
  let σ2 : NNReal := (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal
  have hZ : HasLaw (fun x : ℝ => x) (gaussianReal 0 σ2) (gaussianReal 0 σ2) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 σ2))
  have hclt := scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := gaussianReal 0 σ2) (X := X) (e := e) h a hZ
  have hcoord : TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j)
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 σ2) := by
    simpa [a, dotProduct_single_one] using hclt
  exact BoundedInProbability.of_tendstoInDistribution hcoord

/-- **Inverse-gap projection under the Chapter 7.2 CLT assumptions.**

For every fixed projection vector `a`, the feasible-inverse correction
`(Q̂ₙ⁻¹ - Q⁻¹)√nĝₙ(e)` is `oₚ(1)` after scalar projection. This packages the
coordinatewise product rule with score-coordinate tightness from the CLT. -/
theorem inverseGapProjection_tendstoInMeasure_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  exact inverseGapProjection_tendstoInMeasure_zero_scoreBounded
    (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71 a
    (fun j => scoreCoordinate_sampleCrossMoment_boundedInProbability
      (μ := μ) (X := X) (e := e) h j)

/-- **Scalar totalized-OLS Slutsky remainder under the Chapter 7.2 CLT assumptions.**

The difference between the scaled totalized-OLS projection and its fixed-`Q⁻¹`
score approximation is `oₚ(1)`. This is the direct remainder statement used by
the final scalar CLT. -/
theorem scoreProj_olsBetaStar_remainder_tendstoInMeasure_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a -
          (Real.sqrt (n : ℝ) •
            ((popGram μ X)⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  exact scoreProj_olsBetaStar_remainder_tendstoInMeasure_zero_invGap
    (μ := μ) (X := X) (e := e) (y := y) β a h.toSampleMomentAssumption71 hmodel
    (inverseGapProjection_tendstoInMeasure_zero (μ := μ) (X := X) (e := e) h a)

/-- **CLT for scalar projections of the infeasible leading OLS term.**

Applying the fixed population inverse `Q⁻¹` to `√n · ĝₙ(e)` preserves the
scalar-projection CLT, with the projection vector transformed to `(Q⁻¹)ᵀa`.
The remaining feasible-OLS step is replacing this fixed inverse with the random
`Q̂ₙ⁻¹`, i.e. the multivariate Slutsky/tightness bridge. -/
theorem scoreProj_popGramInv_sampleCrossMoment_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          ((popGram μ X)⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hscore := scoreProj_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a) hZ
  convert hscore using 2 with n
  funext ω
  rw [← Matrix.mulVec_smul, mulVec_dotProduct_right]

/-- **CLT for scalar projections of the infeasible leading OLS term, with `Ω`.**

This is the fixed-`Q⁻¹` leading-term CLT with the Gaussian variance rewritten
as `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. -/
theorem scoreProj_popGramInv_tendstoInDistribution_gaussian_cov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymVar μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          ((popGram μ X)⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hZ' : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν := by
    rw [scoreProj_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)]
    simpa [olsProjectionAsymVar] using hZ
  exact scoreProj_popGramInv_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ'

/-- **Conditional scalar-projection OLS CLT for the totalized estimator.**
Once the scalar Slutsky remainder
`√n(β̂*ₙ - β)·a - √n(Q⁻¹ ĝₙ(e))·a` is known to be `oₚ(1)`, the fixed-`Q⁻¹`
score CLT transfers to the scalar projection of the totalized OLS estimator.

The deterministic roadmap above reduces this remainder to the scaled residual
plus the random-inverse gap; the residual is already controlled, so this
conditional theorem isolates the inverse-gap input used by the later
unconditional scalar result. -/
theorem scoreProj_olsBetaStar_tendstoInDistribution_gaussian_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν)
    (hremainder : TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a -
          (Real.sqrt (n : ℝ) •
            ((popGram μ X)⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0))
    (hfinal_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hfixed := scoreProj_popGramInv_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (n : ℕ) ω =>
      (Real.sqrt (n : ℝ) •
        ((popGram μ X)⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
    (Y := fun (n : ℕ) ω =>
      (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
    (Z := Z) hfixed hremainder hfinal_meas

/-- **Scalar-projection OLS CLT from the inverse-gap condition.**
For every fixed projection vector `a`, the totalized OLS estimator has the
fixed-`Q⁻¹` Gaussian scalar limit once the random-inverse gap projection is
`oₚ(1)`.

This theorem combines the scaled residual control, the inverse-gap reduction,
and Mathlib's Slutsky theorem. It is retained as a useful conditional bridge;
the theorem below discharges the inverse-gap hypothesis from tightness of the
scaled score and `Q̂ₙ⁻¹ →ₚ Q⁻¹`. -/
theorem scoreProj_olsBetaStar_tendstoInDistribution_gaussian_invGap
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν)
    (hinvGap : TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0))
    (hfinal_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hremainder :=
    scoreProj_olsBetaStar_remainder_tendstoInMeasure_zero_invGap
      (μ := μ) (X := X) (e := e) (y := y) β a h.toSampleMomentAssumption71
      hmodel hinvGap
  exact scoreProj_olsBetaStar_tendstoInDistribution_gaussian_remainder
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hZ hremainder hfinal_meas

/-- **Scalar-projection OLS CLT from scaled-score boundedness.**
For every fixed projection vector `a`, the totalized OLS estimator has the
fixed-`Q⁻¹` Gaussian scalar limit once the scaled score coordinates are
`Oₚ(1)`.

Compared with
`scoreProj_olsBetaStar_tendstoInDistribution_gaussian_invGap`,
this theorem discharges the random-inverse gap using the product-rule bridge
and `Q̂ₙ⁻¹ →ₚ Q⁻¹`. The final theorem below obtains `hscoreBounded` from the
score CLT/tightness layer. -/
theorem scoreProj_olsBetaStar_tendstoInDistribution_gaussian_scoreBounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν)
    (hscoreBounded : ∀ j : k,
      BoundedInProbability μ
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j))
    (hfinal_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hinvGap :=
    inverseGapProjection_tendstoInMeasure_zero_scoreBounded
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71 a hscoreBounded
  exact scoreProj_olsBetaStar_tendstoInDistribution_gaussian_invGap
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ hinvGap hfinal_meas

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT.**

For every fixed projection vector `a`, the scaled totalized OLS error has the
Gaussian limit obtained from the fixed-`Q⁻¹` score projection. Compared with
the previous conditional variants, the inverse-gap/tightness premise is now
fully discharged from Theorem 7.2's score CLT. The vector-valued version is
provided earlier by `olsBetaStar_vector_tendstoInDistribution_multivariateGaussian`;
the ordinary-on-nonsingular scalar wrapper is handled by the covariance-form
theorem below. -/
theorem scoreProj_olsBetaStar_tendstoInDistribution_gaussian_finalMeas
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν)
    (hfinal_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  exact scoreProj_olsBetaStar_tendstoInDistribution_gaussian_scoreBounded
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ
    (fun j => scoreCoordinate_sampleCrossMoment_boundedInProbability
      (μ := μ) (X := X) (e := e) h j)
    hfinal_meas

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT.**

This version has no separate measurability premise: the final projection is
measurable by `scoreProj_sqrt_smul_olsBetaStar_sub_aemeasurable`. -/
theorem scoreProj_olsBetaStar_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  exact scoreProj_olsBetaStar_tendstoInDistribution_gaussian_finalMeas
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ
    (scoreProj_sqrt_smul_olsBetaStar_sub_aemeasurable
      (μ := μ) (X := X) (e := e) (y := y) h.toSampleMomentAssumption71 β a hmodel)

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT with `Ω`.**

This restates the final scalar totalized-OLS CLT using the named asymptotic
variance `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. -/
theorem scoreProj_olsBetaStar_tendstoInDistribution_gaussian_cov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymVar μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hZ' : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν := by
    rw [scoreProj_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)]
    simpa [olsProjectionAsymVar] using hZ
  exact scoreProj_olsBetaStar_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ'

/-- **Hansen Theorem 7.9, scalar projections of linear functions of OLS.**

For a fixed matrix `R`, every scalar projection of
`√n · R(β̂*ₙ - β)` is asymptotically normal. This is the linear-functions
special case of the delta-method theorem, obtained by applying the already
proved scalar OLS CLT in the transformed direction `Rᵀc`. -/
theorem scoreProj_linMap_olsBetaStar_tendstoInDistribution_gaussian_cov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (c : q → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymVar μ X e (Rᵀ *ᵥ c)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ c)
      atTop Z (fun _ => μ) ν := by
  have hbase := scoreProj_olsBetaStar_tendstoInDistribution_gaussian_cov
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    h β (Rᵀ *ᵥ c) hmodel hZ
  convert hbase using 2 with n
  funext ω
  rw [← Matrix.mulVec_smul, mulVec_dotProduct_right]

/-- **Hansen Theorem 7.9 for ordinary OLS on nonsingular samples, linear-function face.**

The same scalar-projection CLT for fixed linear maps holds for `olsBetaOrZero`,
which agrees definitionally with `olsBetaStar` in the totalized interface. -/
theorem scoreProj_linMap_olsBetaOrZero_tendstoInDistribution_gaussian_cov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (c : q → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymVar μ X e (Rᵀ *ᵥ c)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ c)
      atTop Z (fun _ => μ) ν := by
  simpa using
    scoreProj_linMap_olsBetaStar_tendstoInDistribution_gaussian_cov
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R c hmodel hZ

/-- **Standard-normal law for the scalar linear t-statistic limit.**

The scalar linear-function CLT produces a Gaussian numerator with variance
`r Vβ r'`. Dividing by the positive population standard error therefore has
standard normal law. -/
theorem olsLinearTLimit_hasLaw_standard
    {μ : Measure Ω}
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (R : Matrix Unit k ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroAsymCov μ X e * Rᵀ) () ())) :
    HasLaw
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroAsymCov μ X e * Rᵀ) () ()))
      (gaussianReal 0 1) ν := by
  let c : ℝ := Real.sqrt ((R * heteroAsymCov μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * heteroAsymCov μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hc : 0 < c := by
    simpa [c] using hse_pos
  have hentry_eq :
      (R * heteroAsymCov μ X e * Rᵀ) () () =
        olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linMapCov_unit_apply_eq_olsProjectionAsymVar
      (μ := μ) (X := X) (e := e) hX R
  have hσ :
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymVar μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroAsymCov μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  simpa [c] using
    hasLaw_gaussianReal_div_const_standard_of_variance_eq
      (ν := ν) (Z := Z) hc hσ hZ

/-- Continuous mapping theorem for absolute values of real distributional limits. -/
theorem tendstoInDistribution_abs_real
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hT : TendstoInDistribution T atTop Z P ν) :
    TendstoInDistribution (fun n ω => |T n ω|) atTop (fun ω => |Z ω|) P ν := by
  simpa [Function.comp_def] using hT.continuous_comp continuous_abs

/-- Relabel a real distributional limit by its law.

If `Tₙ ⇒ Z` under an auxiliary probability space and `Z` has law `η`, then
`Tₙ ⇒ id` under `η`. This is the bookkeeping step used to turn limiting random
variables such as Gaussian quadratic forms into named limit laws such as
`χ²(r)`. -/
theorem tendstoInDistribution_id_of_hasLaw_limit_real
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {η : Measure ℝ} [IsProbabilityMeasure η]
    {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hT : TendstoInDistribution T atTop Z P ν)
    (hZ : HasLaw Z η ν) :
    TendstoInDistribution T atTop (fun x : ℝ => x) P η := by
  refine ⟨hT.forall_aemeasurable, ?_, ?_⟩
  · fun_prop
  · have htarget :
      (⟨ν.map Z, Measure.isProbabilityMeasure_map hT.aemeasurable_limit⟩ :
          ProbabilityMeasure ℝ) =
        ⟨η.map (fun x : ℝ => x), Measure.isProbabilityMeasure_map (by fun_prop)⟩ := by
      apply Subtype.ext
      simp [hZ.map_eq]
    simpa [htarget] using hT.tendsto

omit [Fintype k] [DecidableEq k] in
/-- Lean-only multivariate Wald `χ²` law-identification bridge.

The generic Wald CMT gives convergence to the limiting quadratic form. If that
limiting quadratic form is known to have `χ²(r)` law, this theorem restates the
convergence directly with the named chi-squared limit. The theorem-facing
wrappers below derive this law from Gaussian Mahalanobis results rather than
assuming it as a public hypothesis. -/
theorem waldQuadForm_tendstoInDistribution_chiSquared_limit_hasLaw
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q] [DecidableEq q]
    {r : ℕ} [Fact (0 < r)]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Vhat : ℕ → Ω → Matrix q q ℝ} {V : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw
      (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω)) (chiSquared r) ν) :
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ ((Vhat n ω)⁻¹ *ᵥ T n ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hquad := waldQuadForm_tendstoInDistribution_of_vector_and_covariance
    (μ := μ) (ν := ν) (T := T) (Z := Z) (Vhat := Vhat) (V := V)
    hT hV_meas hV hV_nonsing
  exact tendstoInDistribution_id_of_hasLaw_limit_real hquad hLaw

omit [Fintype k] [DecidableEq k] in
/-- **Wald `χ²` law for an identity-covariance standard-Gaussian limit.**

This removes the law-assumption shortcut in the full-rank identity covariance
case: if the Wald numerator converges to a standard Gaussian vector and the
estimated covariance converges to `I`, the quadratic form converges to
`χ²(r)`. General covariance matrices still require a whitening/Mahalanobis
law bridge. -/
theorem waldQuadForm_tendstoInDistribution_chiSquared_stdGaussian_identity
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {r : ℕ} [Fact (0 < r)]
    {T : ℕ → Ω → Fin r → ℝ}
    {Z : Ω' → EuclideanSpace ℝ (Fin r)}
    {Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    (hT : TendstoInDistribution T atTop
      (fun ω i => (Z ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin r))) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop
      (fun _ => (1 : Matrix (Fin r) (Fin r) ℝ))) :
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ ((Vhat n ω)⁻¹ *ᵥ T n ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  let E := EuclideanSpace ℝ (Fin r)
  let normSq : E → ℝ := fun z => (z : Fin r → ℝ) ⬝ᵥ (z : Fin r → ℝ)
  have hNormMap : HasLaw normSq (chiSquared r) (stdGaussian E) := by
    letI : MeasureSpace E := ⟨stdGaussian E⟩
    haveI : IsProbabilityMeasure (volume : Measure E) := by
      change IsProbabilityMeasure (stdGaussian E)
      infer_instance
    have hId : HasLaw (fun z : E => z) (stdGaussian E) := by
      simpa [id] using (HasLaw.id (μ := stdGaussian E))
    simpa [normSq, E] using
      hasLaw_stdGaussian_normSq_chiSquared (n := r) (Fact.out) hId
  have hLawNorm :
      HasLaw (fun ω => (Z ω : Fin r → ℝ) ⬝ᵥ (Z ω : Fin r → ℝ))
        (chiSquared r) ν := by
    simpa [normSq, E, Function.comp_def] using hNormMap.comp hZ
  have hLaw :
      HasLaw
        (fun ω =>
          (fun i : Fin r => (Z ω : Fin r → ℝ) i) ⬝ᵥ
            (((1 : Matrix (Fin r) (Fin r) ℝ)⁻¹) *ᵥ
              (fun i : Fin r => (Z ω : Fin r → ℝ) i)))
        (chiSquared r) ν := by
    simpa [inv_one, Matrix.one_mulVec] using hLawNorm
  exact waldQuadForm_tendstoInDistribution_chiSquared_limit_hasLaw
    (μ := μ) (ν := ν) (q := Fin r) (r := r)
    (T := T) (Z := fun ω i => (Z ω : Fin r → ℝ) i)
    (Vhat := Vhat) (V := (1 : Matrix (Fin r) (Fin r) ℝ))
    hT hV_meas hV (by simp) hLaw

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 7.13, full-rank Gaussian Wald `χ²` bridge.**

This removes the final-law shortcut for positive-definite covariance limits: if
the Wald numerator converges to a centered multivariate Gaussian with covariance
`V` and the covariance estimator converges to `V`, the Mahalanobis Wald
quadratic form converges to `χ²(r)`. -/
theorem waldQuadForm_tendstoInDistribution_chiSquared_gaussian_mahalanobis
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {r : ℕ} [Fact (0 < r)]
    {T : ℕ → Ω → Fin r → ℝ}
    {Z : Ω' → EuclideanSpace ℝ (Fin r)}
    {Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    (hT : TendstoInDistribution T atTop
      (fun ω i => (Z ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hZ : HasLaw Z (multivariateGaussian 0 V) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_posDef : V.PosDef) :
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ ((Vhat n ω)⁻¹ *ᵥ T n ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hV_nonsing : IsUnit V.det :=
    V.isUnit_iff_isUnit_det.mp hV_posDef.isUnit
  have hLaw : HasLaw
      (fun ω => (fun i : Fin r => (Z ω : Fin r → ℝ) i) ⬝ᵥ
        (V⁻¹ *ᵥ (fun i : Fin r => (Z ω : Fin r → ℝ) i)))
      (chiSquared r) ν := by
    simpa using
      hasLaw_gaussian_mahalanobis_chiSquared (n := r) (Fact.out) hV_posDef hZ
  exact waldQuadForm_tendstoInDistribution_chiSquared_limit_hasLaw
    (μ := μ) (ν := ν) (q := Fin r) (r := r)
    (T := T) (Z := fun ω i => (Z ω : Fin r → ℝ) i)
    (Vhat := Vhat) (V := V)
    hT hV_meas hV hV_nonsing hLaw

/-- Conditional linear-Wald theorem for totalized OLS.

Given a vector score CLT, covariance consistency for the linear restriction
`Rβ`, and an identified chi-squared law for the limiting quadratic form, the
multivariate Wald statistic based on `olsBetaStar` converges to `χ²(r)`. This
packages the OLS vector Slutsky bridge, the linear restriction map, covariance
Slutsky, and the final law relabeling. -/
theorem linMap_olsBetaStar_waldQuadForm_tendstoInDistribution_chiSquared_scoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    {q : Type*} [Fintype q] [DecidableEq q]
    {r : ℕ} [Fact (0 < r)]
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν)
    {Vhat : ℕ → Ω → Matrix q q ℝ} {V : Matrix q q ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw
      (fun ω =>
        (R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω)) ⬝ᵥ
          (V⁻¹ *ᵥ (R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω))))
      (chiSquared r) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hbeta := olsBetaStar_vector_tendstoInDistribution_scoreCLT
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    (Zscore := Zscore) h β hmodel hScore
  have hR : TendstoInDistribution
      (fun (n : ℕ) ω =>
        R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop
      (fun ω => R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω))
      (fun _ => μ) ν := by
    have hcont : Continuous (fun v : k → ℝ => R *ᵥ v) :=
      Continuous.matrix_mulVec continuous_const continuous_id
    simpa [Function.comp_def] using hbeta.continuous_comp hcont
  exact waldQuadForm_tendstoInDistribution_chiSquared_limit_hasLaw
    (μ := μ) (ν := ν)
    (T := fun (n : ℕ) ω =>
      R *ᵥ (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
    (Z := fun ω => R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω))
    (Vhat := Vhat) (V := V)
    hR hV_meas hV hV_nonsing hLaw

/-- Conditional linear-Wald theorem for ordinary OLS.

The same multivariate Wald bridge holds for the ordinary-on-nonsingular wrapper
`olsBetaOrZero`, which agrees pointwise with the totalized estimator in the
Chapter 7 interface. -/
theorem linMap_olsBetaOrZero_waldQuadForm_tendstoInDistribution_chiSquared_scoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    {q : Type*} [Fintype q] [DecidableEq q]
    {r : ℕ} [Fact (0 < r)]
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν)
    {Vhat : ℕ → Ω → Matrix q q ℝ} {V : Matrix q q ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw
      (fun ω =>
        (R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω)) ⬝ᵥ
          (V⁻¹ *ᵥ (R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω))))
      (chiSquared r) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsBetaStar_waldQuadForm_tendstoInDistribution_chiSquared_scoreCLT
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      (Zscore := Zscore) h β R hmodel hScore
      (Vhat := Vhat) (V := V) hV_meas hV hV_nonsing hLaw

/-- **Hansen Theorem 7.13, linear-Wald theorem for totalized OLS.**

This is the public Wald bridge at the current Chapter 7 assumption layer: it
uses the proved vector score CLT rather than taking a vector score convergence
assumption. The only remaining law premise is the law of the limiting quadratic
form itself; the Gaussian/Mahalanobis wrapper below discharges that premise
when the linear restriction limit has a positive-definite Gaussian law. -/
theorem linMap_olsBetaStar_waldQuadForm_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q] [DecidableEq q]
    {r : ℕ} [Fact (0 < r)]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Vhat : ℕ → Ω → Matrix q q ℝ} {V : Matrix q q ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw
      (fun z : EuclideanSpace ℝ k =>
        (R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp)) ⬝ᵥ
          (V⁻¹ *ᵥ (R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp))))
      (chiSquared r) (multivariateGaussian 0 (scoreCovMat μ X e))) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hbeta := olsBetaStar_vector_tendstoInDistribution_multivariateGaussian
    (μ := μ) (X := X) (e := e) (y := y)
    (ScoreCLTConditions.ofSample h) β hmodel
  have hR : TendstoInDistribution
      (fun (n : ℕ) ω =>
        R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop
      (fun z : EuclideanSpace ℝ k => R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp))
      (fun _ => μ) (multivariateGaussian 0 (scoreCovMat μ X e)) := by
    have hcont : Continuous (fun v : k → ℝ => R *ᵥ v) :=
      Continuous.matrix_mulVec continuous_const continuous_id
    simpa [Function.comp_def] using hbeta.continuous_comp hcont
  exact waldQuadForm_tendstoInDistribution_chiSquared_limit_hasLaw
    (μ := μ) (ν := multivariateGaussian 0 (scoreCovMat μ X e))
    (T := fun (n : ℕ) ω =>
      R *ᵥ (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
    (Z := fun z : EuclideanSpace ℝ k => R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp))
    (Vhat := Vhat) (V := V)
    hR hV_meas hV hV_nonsing hLaw

/-- **Hansen Theorem 7.13, ordinary-wrapper linear-Wald theorem.**

The same public Wald bridge for `olsBetaOrZero`, using its pointwise equality
with the totalized estimator. -/
theorem linMap_olsBetaOrZero_waldQuadForm_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q] [DecidableEq q]
    {r : ℕ} [Fact (0 < r)]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Vhat : ℕ → Ω → Matrix q q ℝ} {V : Matrix q q ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw
      (fun z : EuclideanSpace ℝ k =>
        (R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp)) ⬝ᵥ
          (V⁻¹ *ᵥ (R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp))))
      (chiSquared r) (multivariateGaussian 0 (scoreCovMat μ X e))) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsBetaStar_waldQuadForm_tendstoInDistribution_chiSquared
      (μ := μ) (X := X) (e := e) (y := y) h β R hmodel
      (Vhat := Vhat) (V := V) hV_meas hV hV_nonsing hLaw

/-- **Hansen Theorem 7.13, full-rank linear-Wald theorem for totalized OLS.**

This is the non-shortcut version of the linear-Wald wrapper: the limit of the
linear restriction is assumed to be a centered multivariate Gaussian with
positive-definite covariance `V`, and the `χ²(r)` limit is derived from the
Mahalanobis chi-square law. -/
theorem linMap_olsBetaStar_waldChiSquared_scoreCLT_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν)
    {Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_posDef : V.PosDef)
    (hLimitLaw : HasLaw
      (fun ω : Ω' => WithLp.toLp 2 (R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω)))
      (multivariateGaussian 0 V) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hbeta := olsBetaStar_vector_tendstoInDistribution_scoreCLT
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    (Zscore := Zscore) h β hmodel hScore
  have hR : TendstoInDistribution
      (fun (n : ℕ) ω =>
        R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop
      (fun ω => R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω))
      (fun _ => μ) ν := by
    have hcont : Continuous (fun v : k → ℝ => R *ᵥ v) :=
      Continuous.matrix_mulVec continuous_const continuous_id
    simpa [Function.comp_def] using hbeta.continuous_comp hcont
  exact waldQuadForm_tendstoInDistribution_chiSquared_gaussian_mahalanobis
    (μ := μ) (ν := ν) (r := r)
    (T := fun (n : ℕ) ω =>
      R *ᵥ (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
    (Z := fun ω : Ω' => WithLp.toLp 2 (R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω)))
    (Vhat := Vhat) (V := V)
    (by simpa using hR) hLimitLaw hV_meas hV hV_posDef

/-- **Hansen Theorem 7.13, full-rank linear-Wald theorem for ordinary OLS.**

Ordinary-wrapper version of
`linMap_olsBetaStar_waldChiSquared_scoreCLT_gaussian`. -/
theorem linMap_olsBetaOrZero_waldChiSquared_scoreCLT_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν)
    {Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_posDef : V.PosDef)
    (hLimitLaw : HasLaw
      (fun ω : Ω' => WithLp.toLp 2 (R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω)))
      (multivariateGaussian 0 V) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsBetaStar_waldChiSquared_scoreCLT_gaussian
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      (Zscore := Zscore) h β R hmodel hScore
      (Vhat := Vhat) (V := V) hV_meas hV hV_posDef hLimitLaw

/-- Internal Gaussian-limit-law bridge for the full-rank linear-Wald theorem. -/
theorem linMap_olsBetaStar_waldChiSquared_gaussian_limitLaw
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_posDef : V.PosDef)
    (hLimitLaw : HasLaw
      (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 (R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp)))
      (multivariateGaussian 0 V) (multivariateGaussian 0 (scoreCovMat μ X e))) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hbeta := olsBetaStar_vector_tendstoInDistribution_multivariateGaussian
    (μ := μ) (X := X) (e := e) (y := y)
    (ScoreCLTConditions.ofSample h) β hmodel
  have hR : TendstoInDistribution
      (fun (n : ℕ) ω =>
        R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop
      (fun z : EuclideanSpace ℝ k => R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp))
      (fun _ => μ) (multivariateGaussian 0 (scoreCovMat μ X e)) := by
    have hcont : Continuous (fun v : k → ℝ => R *ᵥ v) :=
      Continuous.matrix_mulVec continuous_const continuous_id
    simpa [Function.comp_def] using hbeta.continuous_comp hcont
  exact waldQuadForm_tendstoInDistribution_chiSquared_gaussian_mahalanobis
    (μ := μ) (ν := multivariateGaussian 0 (scoreCovMat μ X e)) (r := r)
    (T := fun (n : ℕ) ω =>
      R *ᵥ (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
    (Z := fun z : EuclideanSpace ℝ k =>
      WithLp.toLp 2 (R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp)))
    (Vhat := Vhat) (V := V)
    (by simpa using hR) hLimitLaw hV_meas hV hV_posDef

/-- Ordinary-wrapper version of
`linMap_olsBetaStar_waldChiSquared_gaussian_limitLaw`. -/
theorem linMap_olsBetaOrZero_waldChiSquared_gaussian_limitLaw
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_posDef : V.PosDef)
    (hLimitLaw : HasLaw
      (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 (R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp)))
      (multivariateGaussian 0 V) (multivariateGaussian 0 (scoreCovMat μ X e))) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsBetaStar_waldChiSquared_gaussian_limitLaw
      (μ := μ) (X := X) (e := e) (y := y) h β R hmodel
      (Vhat := Vhat) (V := V) hV_meas hV hV_posDef hLimitLaw

/-- **Hansen Theorem 7.13, full-rank Gaussian linear-Wald theorem for totalized OLS.**

This is the public non-shortcut Wald theorem: the score CLT is discharged by
Chapter 7's vector Cramér-Wold theorem, the Gaussian linear-image law is proved
once and reused here, and the plug-in covariance only needs to converge to the
actual linear-map sandwich limit. -/
theorem linMap_olsBetaStar_waldChiSquared_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop
      (fun _ => R * heteroAsymCov μ X e * Rᵀ))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  let A : Matrix (Fin r) k ℝ := R * (popGram μ X)⁻¹
  have hLimitLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          WithLp.toLp 2 (R *ᵥ ((popGram μ X)⁻¹ *ᵥ z.ofLp)))
        (multivariateGaussian 0 (R * heteroAsymCov μ X e * Rᵀ))
        (multivariateGaussian 0 (scoreCovMat μ X e)) := by
    have hΩ := scoreCovMat_posSemidef
      (μ := μ) (X := X) (e := e) h.toSampleCLTAssumption72
    have hQinv_transpose : ((popGram μ X)⁻¹)ᵀ = (popGram μ X)⁻¹ := by
      simpa using
        (popGram_inv_isSymm (μ := μ) (X := X) h.toSampleMomentAssumption71.int_outer).eq
    convert
      (hasLaw_multivariateGaussian_zero_linearMap
        (n := k) (q := Fin r) hΩ A) using 1
    · ext z
      simp [A, Matrix.mulVec_mulVec]
    · have hCovEq :
          A * scoreCovMat μ X e * Aᵀ =
            R * heteroAsymCov μ X e * Rᵀ := by
          calc
            A * scoreCovMat μ X e * Aᵀ
                = R * (((popGram μ X)⁻¹ * scoreCovMat μ X e) *
                    ((popGram μ X)⁻¹)ᵀ) * Rᵀ := by
                    simp [A, Matrix.mul_assoc]
            _ = R * (((popGram μ X)⁻¹ * scoreCovMat μ X e) *
                (popGram μ X)⁻¹) * Rᵀ := by
                  rw [hQinv_transpose]
            _ = R * heteroAsymCov μ X e * Rᵀ := by
                  rfl
      simp [hCovEq]
  exact linMap_olsBetaStar_waldChiSquared_gaussian_limitLaw
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h.toSampleCLTAssumption72 β R hmodel (Vhat := Vhat)
    (V := R * heteroAsymCov μ X e * Rᵀ)
    hV_meas hV hV_posDef hLimitLaw

/-- **Hansen Theorem 7.13, full-rank Gaussian linear-Wald theorem for ordinary OLS.**

Ordinary-wrapper version of `linMap_olsBetaStar_waldChiSquared_gaussian`. -/
theorem linMap_olsBetaOrZero_waldChiSquared_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ}
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop
      (fun _ => R * heteroAsymCov μ X e * Rᵀ))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          ((Vhat n ω)⁻¹ *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsBetaStar_waldChiSquared_gaussian
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      h β R hmodel (Vhat := Vhat) hV_meas hV hV_posDef

/-- Generic multivariate Wald packaging for a concrete covariance estimator
family converging to Hansen's heteroskedastic asymptotic covariance. -/
theorem linMap_olsWaldStatStar_tendstoInDistribution_chiSquared_covEst
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (hclt : ScoreCLTConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (covStat : ℕ → Ω → Matrix k k ℝ)
    (hCov_meas : ∀ n, AEStronglyMeasurable (covStat n) μ)
    (hCov : TendstoInMeasure μ covStat atTop
      (fun _ => heteroAsymCov μ X e))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * covStat n ω * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  let Vhat : ℕ → Ω → Matrix (Fin r) (Fin r) ℝ := fun n ω =>
    R * covStat n ω * Rᵀ
  have hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ := by
    intro n
    exact linMapCov_aestronglyMeasurable
      (μ := μ) (R := R) (hCov_meas n)
  have hV : TendstoInMeasure μ Vhat atTop
      (fun _ => R * heteroAsymCov μ X e * Rᵀ) :=
    linMapCov_tendstoInMeasure (μ := μ) (R := R)
      (Vhat := covStat)
      (V := heteroAsymCov μ X e) hCov_meas hCov
  simpa [Vhat] using
    linMap_olsBetaStar_waldChiSquared_gaussian
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      hclt β R hmodel (Vhat := Vhat) hV_meas hV hV_posDef

/-- **Hansen Theorem 7.14, multivariate homoskedastic Wald statistic.**

Under the explicit covariance bridge `V⁰β = Vβ`, the multivariate
homoskedastic Wald statistic for totalized OLS converges to `χ²(r)`. -/
private theorem linMap_olsHomoWaldStatStar_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoAsymCov μ X e =
      heteroAsymCov μ X e)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hV_homo := olsHomoCovStar_tendstoInMeasure
    (μ := μ) (X := X) (e := e) (y := y)
    hvar β hmodel
  have hV_posDef' : (R * heteroAsymCov μ X e * Rᵀ).PosDef := by
    simpa [hVeq] using hV_posDef
  exact linMap_olsWaldStatStar_tendstoInDistribution_chiSquared_covEst
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      hclt β R hmodel
      (covStat := fun n ω =>
        olsHomoCovStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (fun n =>
        olsHomoskedasticCovStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hvar.toSampleMomentAssumption71 β hmodel hX_meas he_meas n)
      (by simpa [hVeq] using hV_homo)
      hV_posDef'

/-- **Hansen Theorem 7.14 for ordinary OLS, multivariate homoskedastic face.** -/
private theorem linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoAsymCov μ X e =
      heteroAsymCov μ X e)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsHomoWaldStatStar_tendstoInDistribution_chiSquared
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      hclt hvar β R hmodel hX_meas he_meas hVeq hV_posDef

/-- **Hansen Theorem 7.14, moment-level multivariate homoskedastic Wald statistic.**

If `Ω = σ²Q`, the multivariate homoskedastic Wald statistic for ordinary OLS
converges to `χ²(r)`. -/
private theorem linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared_scoreCov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hΩ : scoreCovMat μ X e = errorVariance μ e • popGram μ X)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hQ : IsUnit (popGram μ X).det := by
    simpa [popGram] using hvar.toSampleMomentAssumption71.Q_nonsing
  exact linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hclt hvar β R hmodel hX_meas he_meas
    (homoAsymCov_eq_heteroAsymCov
      (μ := μ) (X := X) (e := e) hQ hΩ)
    hV_posDef

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, multivariate homoskedastic Wald statistic from homoskedasticity.**

This variable-facing wrapper derives `Ω = σ²Q` from constant conditional error
variance given `X₀`, then applies the covariance-identity bridge. -/
private theorem linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared_homo
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hΩ := scoreCovMat_eq_errorVariance_smul_popGram_homo
    (μ := μ) (X := X) (e := e)
    hclt.toSampleCLTAssumption72 hvar.toSampleVarianceAssumption74 hX0 hhomo
  exact linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared_scoreCov
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hclt hvar β R hmodel hX_meas he_meas hΩ hV_posDef

namespace HomoskedasticInferenceConditions

/-- Packaged multivariate homoskedastic Wald statistic with an explicit covariance bridge. -/
theorem linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {β : k → ℝ} {r : ℕ} [Fact (0 < r)]
    (h : HomoskedasticInferenceConditions μ X e y β)
    (R : Matrix (Fin r) k ℝ)
    (hVeq : homoAsymCov μ X e = heteroAsymCov μ X e)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  HansenEconometrics.linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h.score h.variance β R h.model h.x_aestronglyMeasurable
    h.e_aestronglyMeasurable hVeq hV_posDef

end HomoskedasticInferenceConditions

namespace HomoskedasticErrorInferenceConditions

/-- Packaged multivariate homoskedastic Wald statistic deriving the covariance bridge internally. -/
theorem linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {β : k → ℝ} {r : ℕ} [Fact (0 < r)]
    (h : HomoskedasticErrorInferenceConditions μ X e y β)
    (R : Matrix (Fin r) k ℝ)
    (hV_posDef : (R * homoAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHomoCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.x0_measurable)) :=
    h.sigmaFinite_x0
  exact HansenEconometrics.linMap_olsHomoWaldStatOrZero_tendstoInDistribution_chiSquared_homo
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h.score h.variance β R h.model h.x_aestronglyMeasurable
    h.e_aestronglyMeasurable h.x0_measurable h.homoskedastic hV_posDef

end HomoskedasticErrorInferenceConditions

/-- Multivariate HC0 Wald statistic for totalized OLS. -/
private theorem linMap_olsHC0WaldStatStar_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  exact linMap_olsWaldStatStar_tendstoInDistribution_chiSquared_covEst
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      (ScoreCLTConditions.ofSample h.toSampleCLTAssumption72) β R hmodel
      (covStat := fun n ω =>
        olsHetCovStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (fun n =>
        olsHetCovStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          h.toSampleMomentAssumption71 β hmodel hX_meas he_meas n)
      (olsHetCovStar_tendstoInMeasure_of_bddWts_components
        (μ := μ) (X := X) (e := e) (y := y)
        h.toSampleHC0Assumption76 β hmodel hX_meas he_meas hCrossWeight hQuadWeight)
      hV_posDef

/-- Multivariate HC0 Wald statistic for ordinary OLS. -/
private theorem linMap_olsHC0WaldStatOrZero_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsHC0WaldStatStar_tendstoInDistribution_chiSquared
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hV_posDef

/-- Multivariate HC1 Wald statistic for totalized OLS. -/
private theorem linMap_olsHC1WaldStatStar_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  exact linMap_olsWaldStatStar_tendstoInDistribution_chiSquared_covEst
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      (ScoreCLTConditions.ofSample h.toSampleCLTAssumption72) β R hmodel
      (covStat := fun n ω =>
        olsHetCovHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (fun n =>
        olsHC1CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          h.toSampleMomentAssumption71 β hmodel hX_meas he_meas n)
      (olsHetCovHC1Star_tendstoInMeasure_of_bddWts_components
        (μ := μ) (X := X) (e := e) (y := y)
        h.toSampleHC0Assumption76 β hmodel hX_meas he_meas hCrossWeight hQuadWeight)
      hV_posDef

/-- Multivariate HC1 Wald statistic for ordinary OLS. -/
private theorem linMap_olsHC1WaldStatOrZero_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsHC1WaldStatStar_tendstoInDistribution_chiSquared
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hV_posDef

/-- Multivariate HC2 Wald statistic for totalized OLS. -/
private theorem linMap_olsHC2WaldStatStar_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  exact linMap_olsWaldStatStar_tendstoInDistribution_chiSquared_covEst
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      (ScoreCLTConditions.ofSample h.toSampleCLTAssumption72) β R hmodel
      (covStat := fun n ω =>
        olsHetCovHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (fun n =>
        olsHC2CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          h.toSampleMomentAssumption71 β hmodel hX_meas he_meas n)
      (olsHetCovHC2Star_tendstoInMeasure_of_bddWts_components_maxLev
        (μ := μ) (X := X) (e := e) (y := y)
        h β hmodel hX_meas he_meas hCrossWeight hQuadWeight hMax)
      hV_posDef

/-- Multivariate HC2 Wald statistic for ordinary OLS. -/
private theorem linMap_olsHC2WaldStatOrZero_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsHC2WaldStatStar_tendstoInDistribution_chiSquared
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight
      hMax hV_posDef

/-- Multivariate HC3 Wald statistic for totalized OLS. -/
private theorem linMap_olsHC3WaldStatStar_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  exact linMap_olsWaldStatStar_tendstoInDistribution_chiSquared_covEst
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      (ScoreCLTConditions.ofSample h.toSampleCLTAssumption72) β R hmodel
      (covStat := fun n ω =>
        olsHetCovHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (fun n =>
        olsHC3CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          h.toSampleMomentAssumption71 β hmodel hX_meas he_meas n)
      (olsHetCovHC3Star_tendstoInMeasure_of_bddWts_components_maxLev
        (μ := μ) (X := X) (e := e) (y := y)
        h β hmodel hX_meas he_meas hCrossWeight hQuadWeight hMax)
      hV_posDef

/-- Multivariate HC3 Wald statistic for ordinary OLS. -/
private theorem linMap_olsHC3WaldStatOrZero_tendstoInDistribution_chiSquared
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa using
    linMap_olsHC3WaldStatStar_tendstoInDistribution_chiSquared
      (μ := μ) (X := X) (e := e) (y := y) (r := r)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight
      hMax hV_posDef

/-- Packaged HC0 multivariate Wald statistic for totalized OLS.

This is the 7.13 robust-Wald wrapper with the feasible HC residual-remainder
conditions bundled in `FeasibleHCRemainderConditions`. -/
private theorem linMap_hc0_wald_star_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_olsHC0WaldStatStar_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β R hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hV_posDef

set_option linter.style.longLine false in
/-- Packaged HC0 multivariate Wald statistic for ordinary OLS. -/
private theorem linMap_hc0_wald_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_olsHC0WaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β R hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hV_posDef

/-- Packaged HC1 multivariate Wald statistic for totalized OLS. -/
private theorem linMap_hc1_wald_star_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_olsHC1WaldStatStar_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β R hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hV_posDef

set_option linter.style.longLine false in
/-- Packaged HC1 multivariate Wald statistic for ordinary OLS. -/
private theorem linMap_hc1_wald_feasible_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hc : FeasibleHCRemainderConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_olsHC1WaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β R hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hV_posDef

/-- Packaged HC2 multivariate Wald statistic for totalized OLS. -/
private theorem linMap_hc2_wald_star_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_olsHC2WaldStatStar_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β R hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hc.maxLeverage_tendsto hV_posDef

/-- Packaged HC2 multivariate Wald statistic for ordinary OLS. -/
private theorem linMap_hc2_wald_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_olsHC2WaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β R hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hc.maxLeverage_tendsto hV_posDef

/-- Packaged HC3 multivariate Wald statistic for totalized OLS. -/
private theorem linMap_hc3_wald_star_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_olsHC3WaldStatStar_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β R hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hc.maxLeverage_tendsto hV_posDef

/-- Packaged HC3 multivariate Wald statistic for ordinary OLS. -/
private theorem linMap_hc3_wald_feasible_leverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix (Fin r) k ℝ)
    (hc : FeasibleHCLeverageConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_olsHC3WaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    h β R hc.model hc.x_aestronglyMeasurable hc.e_aestronglyMeasurable
    hc.crossWeight_bounded hc.quadWeight_bounded hc.maxLeverage_tendsto hV_posDef

set_option linter.style.longLine false in
/-- Compact robust-moment HC0 multivariate Wald statistic for totalized OLS. -/
theorem linMap_olsHC0WaldStatStar_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_hc0_wald_star_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hV_posDef

set_option linter.style.longLine false in
/-- Compact robust-moment HC0 multivariate Wald statistic for ordinary OLS. -/
theorem linMap_olsHC0WaldStatOrZero_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_hc0_wald_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hV_posDef

set_option linter.style.longLine false in
/-- Compact robust-moment HC1 multivariate Wald statistic for totalized OLS. -/
theorem linMap_olsHC1WaldStatStar_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_hc1_wald_star_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hV_posDef

set_option linter.style.longLine false in
/-- Compact robust-moment HC1 multivariate Wald statistic for ordinary OLS. -/
theorem linMap_olsHC1WaldStatOrZero_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_hc1_wald_feasible_remainder
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCRemainderConditions hV_posDef

set_option linter.style.longLine false in
/-- Compact robust-moment HC2 multivariate Wald statistic for totalized OLS. -/
theorem linMap_olsHC2WaldStatStar_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_hc2_wald_star_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hV_posDef

set_option linter.style.longLine false in
/-- Compact robust-moment HC2 multivariate Wald statistic for ordinary OLS. -/
theorem linMap_olsHC2WaldStatOrZero_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_hc2_wald_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hV_posDef

set_option linter.style.longLine false in
/-- Compact robust-moment HC3 multivariate Wald statistic for totalized OLS. -/
theorem linMap_olsHC3WaldStatStar_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_hc3_wald_star_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hV_posDef

set_option linter.style.longLine false in
/-- Compact robust-moment HC3 multivariate Wald statistic for ordinary OLS. -/
theorem linMap_olsHC3WaldStatOrZero_tendstoInDistribution_chiSquared_of_robustFeasibleHCMomentConditions
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {r : ℕ} [Fact (0 < r)]
    (β : k → ℝ) (R : Matrix (Fin r) k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hV_posDef : (R * heteroAsymCov μ X e * Rᵀ).PosDef) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (R *ᵥ (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
          (((R * olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)⁻¹) *ᵥ
            (R *ᵥ (Real.sqrt (n : ℝ) •
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)))))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) :=
  linMap_hc3_wald_feasible_leverage
    (μ := μ) (X := X) (e := e) (y := y) (r := r)
    hm.toRobustCovarianceConsistencyConditions β R
    hm.toFeasibleHCLeverageConditions hV_posDef

end Assumption72

end HansenEconometrics
