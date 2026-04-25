import HansenEconometrics.Chapter7Asymptotics.RobustCovariance

/-!
# Chapter 7 Asymptotics: Normality

Scalar and vector distributional bridges for OLS asymptotic normality, plus the
conditional multivariate Wald continuous-mapping layer.
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
/-- Borel σ-algebra on `Matrix k k ℝ` inherited from the elementwise-L∞ norm,
reintroduced for Chapter 7 submodules using covariance-matrix random variables. -/
@[reducible]
private noncomputable def matrixBorelMeasurableSpace72 :
    MeasurableSpace (Matrix k k ℝ) := borel _

attribute [local instance] matrixBorelMeasurableSpace72

omit [Fintype k] [DecidableEq k] in
private lemma matrixBorelSpace72 : BorelSpace (Matrix k k ℝ) := ⟨rfl⟩

attribute [local instance] matrixBorelSpace72

omit [DecidableEq k] in
/-- Move a fixed matrix multiplication from the left side of a dot product to the right side. -/
private theorem mulVec_dotProduct_right {q : Type*} [Fintype q]
    (M : Matrix q k ℝ) (v : k → ℝ) (a : q → ℝ) :
    (M *ᵥ v) ⬝ᵥ a = v ⬝ᵥ (Mᵀ *ᵥ a) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]

/-- **Hansen Theorem 7.2, scalar-projection score CLT.**

For every fixed vector `a`, the projected score sum
`(1 / √n) ∑_{i<n} (eᵢXᵢ)·a` converges in distribution to the Gaussian with the
matching scalar variance. This is the one-dimensional CLT supplied by Mathlib,
specialized to the score projections that appear in OLS asymptotic normality.

This is not yet the literal vector-valued statement of Theorem 7.2, nor does it
separately expose the textbook `Ω < ∞` conclusion. It is the Cramér-Wold-facing
piece needed to build that vector theorem. -/
theorem scoreProjection_sum_tendstoInDistribution_gaussian
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
  have hmean := scoreProjection_integral_zero (μ := μ)
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

This is the same CLT as `scoreProjection_sum_tendstoInDistribution_gaussian`,
rewritten in Hansen's notation as `√n · ĝₙ(e)` where
`ĝₙ(e) = n⁻¹∑ eᵢXᵢ`.

Status: this is the main formalized face of Theorem 7.2 at present. The full
vector-valued CLT is still pending. -/
theorem scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian
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
  have hsum := scoreProjection_sum_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ
  convert hsum using 2 with n
  funext ω
  rw [sqrt_smul_sampleCrossMoment_stackRegressors_stackErrors_eq_inv_sqrt_sum]
  simp [sum_dotProduct, smul_eq_mul]

/-- **Hansen Theorem 7.2, scalar-projection score CLT with `Ω`.**

This is `scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian`
with the Gaussian variance rewritten as the quadratic form
`a' Ω a`, where `Ω = scoreCovarianceMatrix μ X e`. -/
theorem scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (a ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ a)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hZ' : HasLaw Z
      (gaussianReal 0 (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal) ν := by
    rw [scoreProjection_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h a]
    exact hZ
  exact scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ'

/-- **Hansen Theorem 7.2, all scalar projections with `Ω`.**

This packages the current Cramér-Wold-facing endpoint: for every fixed
direction `a`, the scalar projection of `√n · ĝₙ(e)` has Gaussian limit with
variance `a' Ω a`.  The remaining gap to the literal textbook statement is the
reverse Cramér-Wold/vector-valued convergence wrapper. -/
theorem scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian_covariance_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (a ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ a)).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) h a (hZ a)

/-- **Hansen Theorem 7.3, feasible leading-score vector Slutsky bridge.**

Conditional on a vector-valued score CLT for `√n · ĝₙ(e)`, the feasible OLS
leading term formed with the random inverse Gram matrix satisfies
`Q̂ₙ⁻¹√nĝₙ(e) ⇒ Q⁻¹Z`. This is the vector version of the inverse-gap step:
the remaining full OLS theorem only has to add the already-negligible
singular-event residual. -/
theorem feasibleScore_tendstoInDistribution_of_scoreCLT
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
theorem olsBetaStar_vector_tendstoInDistribution_of_scoreCLT
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
  have hFeasible := feasibleScore_tendstoInDistribution_of_scoreCLT
    (μ := μ) (ν := ν) (X := X) (e := e) (Zscore := Zscore) h hScore
  have hResidual :=
    sqrt_smul_olsBetaStar_sub_sub_feasibleScore_tendstoInMeasure_zero
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
theorem olsBetaOrZero_vector_tendstoInDistribution_of_scoreCLT
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
  have hstar := olsBetaStar_vector_tendstoInDistribution_of_scoreCLT
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
    rw [olsBetaOrZero_eq_olsBetaStar])

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
  have hclt := scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian
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
  exact inverseGapProjection_tendstoInMeasure_zero_of_scoreBounded
    (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71 a
    (fun j => scoreCoordinate_sampleCrossMoment_boundedInProbability
      (μ := μ) (X := X) (e := e) h j)

/-- **Scalar totalized-OLS Slutsky remainder under the Chapter 7.2 CLT assumptions.**

The difference between the scaled totalized-OLS projection and its fixed-`Q⁻¹`
score approximation is `oₚ(1)`. This is the direct remainder statement used by
the final scalar CLT. -/
theorem scoreProjection_olsBetaStar_remainder_tendstoInMeasure_zero
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
  exact scoreProjection_olsBetaStar_remainder_tendstoInMeasure_zero_of_inverseGap
    (μ := μ) (X := X) (e := e) (y := y) β a h.toSampleMomentAssumption71 hmodel
    (inverseGapProjection_tendstoInMeasure_zero (μ := μ) (X := X) (e := e) h a)

/-- **CLT for scalar projections of the infeasible leading OLS term.**

Applying the fixed population inverse `Q⁻¹` to `√n · ĝₙ(e)` preserves the
scalar-projection CLT, with the projection vector transformed to `(Q⁻¹)ᵀa`.
The remaining feasible-OLS step is replacing this fixed inverse with the random
`Q̂ₙ⁻¹`, i.e. the multivariate Slutsky/tightness bridge. -/
theorem scoreProjection_popGramInv_mulVec_sampleCrossMoment_tendstoInDistribution_gaussian
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
  have hscore := scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a) hZ
  convert hscore using 2 with n
  funext ω
  rw [← Matrix.mulVec_smul, mulVec_dotProduct_right]

/-- **CLT for scalar projections of the infeasible leading OLS term, with `Ω`.**

This is the fixed-`Q⁻¹` leading-term CLT with the Gaussian variance rewritten
as `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. -/
theorem scoreProjection_popGramInv_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
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
    rw [scoreProjection_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)]
    simpa [olsProjectionAsymptoticVariance] using hZ
  exact scoreProjection_popGramInv_mulVec_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ'

/-- **Conditional scalar-projection OLS CLT for the totalized estimator.**
Once the scalar Slutsky remainder
`√n(β̂*ₙ - β)·a - √n(Q⁻¹ ĝₙ(e))·a` is known to be `oₚ(1)`, the fixed-`Q⁻¹`
score CLT transfers to the scalar projection of the totalized OLS estimator.

The deterministic roadmap above reduces this remainder to the scaled residual
plus the random-inverse gap; the residual is already controlled, so this
conditional theorem isolates the inverse-gap input used by the later
unconditional scalar result. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_remainder
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
  have hfixed := scoreProjection_popGramInv_mulVec_sampleCrossMoment_tendstoInDistribution_gaussian
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
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_inverseGap
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
    scoreProjection_olsBetaStar_remainder_tendstoInMeasure_zero_of_inverseGap
      (μ := μ) (X := X) (e := e) (y := y) β a h.toSampleMomentAssumption71
      hmodel hinvGap
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_remainder
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hZ hremainder hfinal_meas

/-- **Scalar-projection OLS CLT from scaled-score boundedness.**
For every fixed projection vector `a`, the totalized OLS estimator has the
fixed-`Q⁻¹` Gaussian scalar limit once the scaled score coordinates are
`Oₚ(1)`.

Compared with
`scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_inverseGap`,
this theorem discharges the random-inverse gap using the product-rule bridge
and `Q̂ₙ⁻¹ →ₚ Q⁻¹`. The final theorem below obtains `hscoreBounded` from the
score CLT/tightness layer. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_scoreBounded
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
    inverseGapProjection_tendstoInMeasure_zero_of_scoreBounded
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71 a hscoreBounded
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_inverseGap
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ hinvGap hfinal_meas

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT.**

For every fixed projection vector `a`, the scaled totalized OLS error has the
Gaussian limit obtained from the fixed-`Q⁻¹` score projection. Compared with
the previous conditional variants, the inverse-gap/tightness premise is now
fully discharged from Theorem 7.2's score CLT. The remaining textbook-facing
work is the vector Cramér-Wold packaging; the ordinary-on-nonsingular wrapper
is handled by the covariance-form theorem below. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_finalMeas
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
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_scoreBounded
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ
    (fun j => scoreCoordinate_sampleCrossMoment_boundedInProbability
      (μ := μ) (X := X) (e := e) h j)
    hfinal_meas

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT.**

This version has no separate measurability premise: the final projection is
measurable by `scoreProjection_sqrt_smul_olsBetaStar_sub_aemeasurable`. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian
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
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_finalMeas
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ
    (scoreProjection_sqrt_smul_olsBetaStar_sub_aemeasurable
      (μ := μ) (X := X) (e := e) (y := y) h.toSampleMomentAssumption71 β a hmodel)

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT with `Ω`.**

This restates the final scalar totalized-OLS CLT using the named asymptotic
variance `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hZ' : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν := by
    rw [scoreProjection_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)]
    simpa [olsProjectionAsymptoticVariance] using hZ
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ'

/-- **Hansen Theorem 7.9, scalar projections of linear functions of OLS.**

For a fixed matrix `R`, every scalar projection of
`√n · R(β̂*ₙ - β)` is asymptotically normal. This is the linear-functions
special case of the delta-method theorem, obtained by applying the already
proved scalar OLS CLT in the transformed direction `Rᵀc`. -/
theorem scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (c : q → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ c)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ c)
      atTop Z (fun _ => μ) ν := by
  have hbase := scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    h β (Rᵀ *ᵥ c) hmodel hZ
  convert hbase using 2 with n
  funext ω
  rw [← Matrix.mulVec_smul, mulVec_dotProduct_right]

/-- **Hansen Theorem 7.9 for ordinary OLS on nonsingular samples, linear-function face.**

The same scalar-projection CLT for fixed linear maps holds for `olsBetaOrZero`,
which agrees definitionally with `olsBetaStar` in the totalized interface. -/
theorem scoreProjection_linearMap_olsBetaOrZero_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (c : q → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ c)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ c)
      atTop Z (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R c hmodel hZ

/-- **Standard-normal law for the scalar linear t-statistic limit.**

The scalar linear-function CLT produces a Gaussian numerator with variance
`r Vβ r'`. Dividing by the positive population standard error therefore has
standard normal law. -/
theorem olsLinearTStatisticLimit_hasLaw_standard
    {μ : Measure Ω}
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (R : Matrix Unit k ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    HasLaw
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (gaussianReal 0 1) ν := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hc : 0 < c := by
    simpa [c] using hse_pos
  have hentry_eq :
      (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
        olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) hX R
  have hσ :
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () :=
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
theorem waldQuadraticForm_tendstoInDistribution_chiSquared_of_limit_hasLaw
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
  have hquad := waldQuadraticForm_tendstoInDistribution_of_vector_and_covariance
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
theorem waldQuadraticForm_tendstoInDistribution_chiSquared_of_stdGaussian_identity
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
  exact waldQuadraticForm_tendstoInDistribution_chiSquared_of_limit_hasLaw
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
theorem waldQuadraticForm_tendstoInDistribution_chiSquared_of_gaussian_mahalanobis
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
  exact waldQuadraticForm_tendstoInDistribution_chiSquared_of_limit_hasLaw
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
theorem linearMap_olsBetaStar_waldQuadraticForm_tendstoInDistribution_chiSquared_of_scoreCLT
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
  have hbeta := olsBetaStar_vector_tendstoInDistribution_of_scoreCLT
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
  exact waldQuadraticForm_tendstoInDistribution_chiSquared_of_limit_hasLaw
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
theorem linearMap_olsBetaOrZero_waldQuadraticForm_tendstoInDistribution_chiSquared_of_scoreCLT
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
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    linearMap_olsBetaStar_waldQuadraticForm_tendstoInDistribution_chiSquared_of_scoreCLT
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      (Zscore := Zscore) h β R hmodel hScore
      (Vhat := Vhat) (V := V) hV_meas hV hV_nonsing hLaw

/-- **Hansen Theorem 7.13, full-rank linear-Wald theorem for totalized OLS.**

This is the non-shortcut version of the linear-Wald wrapper: the limit of the
linear restriction is assumed to be a centered multivariate Gaussian with
positive-definite covariance `V`, and the `χ²(r)` limit is derived from the
Mahalanobis chi-square law. -/
theorem linearMap_olsBetaStar_waldChiSquared_of_scoreCLT_gaussian
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
  have hbeta := olsBetaStar_vector_tendstoInDistribution_of_scoreCLT
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
  exact waldQuadraticForm_tendstoInDistribution_chiSquared_of_gaussian_mahalanobis
    (μ := μ) (ν := ν) (r := r)
    (T := fun (n : ℕ) ω =>
      R *ᵥ (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
    (Z := fun ω : Ω' => WithLp.toLp 2 (R *ᵥ ((popGram μ X)⁻¹ *ᵥ Zscore ω)))
    (Vhat := Vhat) (V := V)
    (by simpa using hR) hLimitLaw hV_meas hV hV_posDef

/-- **Hansen Theorem 7.13, full-rank linear-Wald theorem for ordinary OLS.**

Ordinary-wrapper version of
`linearMap_olsBetaStar_waldChiSquared_of_scoreCLT_gaussian`. -/
theorem linearMap_olsBetaOrZero_waldChiSquared_of_scoreCLT_gaussian
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
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    linearMap_olsBetaStar_waldChiSquared_of_scoreCLT_gaussian
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      (Zscore := Zscore) h β R hmodel hScore
      (Vhat := Vhat) (V := V) hV_meas hV hV_posDef hLimitLaw

end Assumption72

end HansenEconometrics
