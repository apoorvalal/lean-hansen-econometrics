import HansenEconometrics.Chapter7Asymptotics.Basic

/-!
# Chapter 7 Asymptotics: Consistency

Moment assumptions and convergence-in-probability results for OLS consistency,
continuous transformations, and residual variance consistency.
-/

open scoped Matrix Real

namespace HansenEconometrics

open Matrix

section Assumption71

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {n : Type*} [Fintype n]
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
/-- Borel σ-algebra on `Matrix k k ℝ` inherited from the elementwise-L∞ norm.
Section-scoped so the choice of norm stays local. -/
@[reducible]
private noncomputable def matrixBorelMeasurableSpace :
    MeasurableSpace (Matrix k k ℝ) := borel _

attribute [local instance] matrixBorelMeasurableSpace

omit [Fintype k] [DecidableEq k] in
private lemma matrixBorelSpace : BorelSpace (Matrix k k ℝ) := ⟨rfl⟩

attribute [local instance] matrixBorelSpace

/-- Moment-level sufficient assumptions for the current Chapter 7.1 consistency proof.

This deliberately packages only the transformed sequences needed by the WLLN steps:
outer products `Xᵢ Xᵢᵀ` and cross products `eᵢ Xᵢ`. It is implied by suitable iid
sample assumptions, but it is not itself a literal encoding of Hansen
Assumption 7.1. -/
structure SampleMomentAssumption71 (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) where
  /-- Pairwise independence of the outer-product sequence `X i (X i)ᵀ`. -/
  indep_outer :
    Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => Matrix.vecMulVec (X i ω) (X i ω)))
  /-- Pairwise independence of the cross-product sequence `e i • X i`. -/
  indep_cross :
    Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • X i ω))
  /-- Identical distribution of the outer products. -/
  ident_outer : ∀ i,
    IdentDistrib (fun ω => Matrix.vecMulVec (X i ω) (X i ω))
                 (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ μ
  /-- Identical distribution of the cross products. -/
  ident_cross : ∀ i,
    IdentDistrib (fun ω => e i ω • X i ω) (fun ω => e 0 ω • X 0 ω) μ μ
  /-- Second moments on `X` (so `X Xᵀ` is integrable). -/
  int_outer : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ
  /-- First-moment integrability of `e X`. -/
  int_cross : Integrable (fun ω => e 0 ω • X 0 ω) μ
  /-- Population Gram matrix `Q := 𝔼[X Xᵀ]` is nonsingular. -/
  Q_nonsing : IsUnit (μ[fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)]).det
  /-- Population orthogonality `𝔼[e X] = 0`. -/
  orthogonality : μ[fun ω => e 0 ω • X 0 ω] = 0

/-- Additional squared-error WLLN assumptions used for Hansen Theorem 7.4.

The textbook Assumption 7.1 implies these for iid observations with finite
second moments; this structure records exactly what the current Lean proof
needs for the residual-variance consistency layer. -/
structure SampleVarianceAssumption74 (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends SampleMomentAssumption71 μ X e where
  /-- Pairwise independence of the true squared-error sequence. -/
  indep_error_sq : Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω ^ 2))
  /-- Identical distribution of the true squared errors. -/
  ident_error_sq : ∀ i,
    IdentDistrib (fun ω => e i ω ^ 2) (fun ω => e 0 ω ^ 2) μ μ
  /-- Integrability of the true squared error. -/
  int_error_sq : Integrable (fun ω => e 0 ω ^ 2) μ

/-- Descriptive public alias for the current Lean proof package behind Hansen
Assumption 7.1 / Theorem 7.1.

This is a moment-level sufficient bundle for the current consistency proof, not
a literal iid-sample encoding. The underlying `SampleMomentAssumption71` name is
kept as proof infrastructure. -/
abbrev LeastSquaresConsistencyConditions (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) :=
  SampleMomentAssumption71 μ X e

/-- Descriptive public alias for the current Lean proof package behind Hansen
Theorem 7.4 / 7.5.

This extends the consistency bundle with the squared-error WLLN hypotheses used
for residual-variance and homoskedastic covariance consistency. It is still a
sufficient moment-level package rather than a literal textbook encoding. -/
abbrev ErrorVarianceConsistencyConditions (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) :=
  SampleVarianceAssumption74 μ X e

/-- The population Gram matrix `Q := 𝔼[X Xᵀ]`. -/
noncomputable def popGram (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) : Matrix k k ℝ :=
  μ[fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)]

omit [DecidableEq k] in
/-- The population Gram matrix is symmetric whenever the outer product is integrable. -/
theorem popGram_isSymm
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ))
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ) :
    (popGram μ X).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  calc
    (popGram μ X) j i
        = ∫ ω, (Matrix.vecMulVec (X 0 ω) (X 0 ω)) j i ∂μ := by
          rw [popGram]
          exact integral_apply_apply
            (μ := μ) (f := fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) hX j i
    _ = ∫ ω, (Matrix.vecMulVec (X 0 ω) (X 0 ω)) i j ∂μ := by
          congr with ω
          simp [Matrix.vecMulVec_apply, mul_comm]
    _ = (popGram μ X) i j := by
          rw [popGram]
          exact (integral_apply_apply
            (μ := μ) (f := fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) hX i j).symm

/-- The totalized inverse of the population Gram matrix is symmetric. -/
theorem popGram_inv_isSymm
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ))
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ) :
    ((popGram μ X)⁻¹).IsSymm :=
  (popGram_isSymm μ X hX).inv

/-- The textbook error variance `σ² := E[e²]` used in Theorem 7.4. -/
noncomputable def errorVariance (μ : Measure Ω) (e : ℕ → Ω → ℝ) : ℝ :=
  μ[fun ω => e 0 ω ^ 2]

/-- **WLLN for the sample Gram.** Under the moment-level assumptions, the sample
Gram matrix of the stacked design converges in probability to the population Gram `Q`. -/
theorem sampleGram_stackRegressors_tendstoInMeasure_popGram
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleGram (stackRegressors X n ω))
      atTop
      (fun _ => popGram μ X) := by
  have hfun_eq : (fun n ω => sampleGram (stackRegressors X n ω)) =
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
    funext n ω
    rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
  rw [hfun_eq]
  exact tendstoInMeasure_wlln
    (fun i ω => Matrix.vecMulVec (X i ω) (X i ω))
    h.int_outer h.indep_outer h.ident_outer

/-- Measurability of the stacked sample Gram under the Chapter 7.1 moment layer. -/
theorem sampleGram_stackRegressors_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
  have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
      (fun ω => (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
    funext ω
    rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
  rw [hform]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable

/-- Measurability of the stacked sample cross moment under the Chapter 7.1 moment layer. -/
theorem sampleCrossMoment_stackRegressors_stackErrors_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
  have hform : (fun ω => sampleCrossMoment (stackRegressors X n ω)
        (stackErrors e n ω)) =
      (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω) := by
    funext ω
    rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
        sum_fin_eq_sum_range_smul]
  rw [hform]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((h.ident_cross i).integrable_iff.mpr h.int_cross).aestronglyMeasurable

/-- **CMT for the inverse sample Gram.** Under the moment-level assumptions,
`Q̂ₙ⁻¹ →ₚ Q⁻¹`. -/
theorem sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω => (sampleGram (stackRegressors X n ω))⁻¹)
      atTop (fun _ => (popGram μ X)⁻¹) := by
  have hGram := sampleGram_stackRegressors_tendstoInMeasure_popGram h
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    exact sampleGram_stackRegressors_aestronglyMeasurable h n
  exact tendstoInMeasure_matrix_inv hGram_meas hGram (fun _ => h.Q_nonsing)

/-- **WLLN for the sample cross moment.** Under the moment-level assumptions, the sample
cross moment `ĝₙ = n⁻¹ ∑ eᵢ Xᵢ` of the stacked design converges in probability to
`0`, since the population cross moment `𝔼[e X] = 0` by the orthogonality axiom. -/
theorem sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => 0) := by
  have hfun_eq : (fun n ω => sampleCrossMoment (stackRegressors X n ω)
        (stackErrors e n ω)) =
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, e i ω • X i ω) := by
    funext n ω
    rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
        sum_fin_eq_sum_range_smul]
  rw [hfun_eq, show (fun _ : Ω => (0 : k → ℝ)) =
      (fun _ : Ω => μ[fun ω => e 0 ω • X 0 ω]) by rw [h.orthogonality]]
  exact tendstoInMeasure_wlln
    (fun i ω => e i ω • X i ω)
    h.int_cross h.indep_cross h.ident_cross

/-- **Theorem 7.4 squared-error WLLN.**

Under the 7.4 squared-error assumptions, the sample average of the true squared
errors converges in probability to `σ² = E[e₀²]`. -/
theorem sampleErrorSecondMoment_stackErrors_tendstoInMeasure_errorVariance
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleErrorSecondMoment (stackErrors e n ω))
      atTop
      (fun _ => errorVariance μ e) := by
  have hfun_eq : (fun n ω => sampleErrorSecondMoment (stackErrors e n ω)) =
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, e i ω ^ 2) := by
    funext n ω
    rw [sampleErrorSecondMoment_stackErrors_eq_avg]
  rw [hfun_eq]
  simpa [errorVariance, smul_eq_mul] using
    tendstoInMeasure_wlln
      (fun i ω => e i ω ^ 2)
      h.int_error_sq h.indep_error_sq h.ident_error_sq

/-- Centered form of the Theorem 7.4 squared-error WLLN. -/
theorem sampleErrorSecondMoment_stackErrors_sub_errorVariance_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleErrorSecondMoment (stackErrors e n ω) - errorVariance μ e)
      atTop
      (fun _ => 0) := by
  have hraw :=
    sampleErrorSecondMoment_stackErrors_tendstoInMeasure_errorVariance
      (μ := μ) (X := X) (e := e) h
  rw [tendstoInMeasure_iff_dist] at hraw ⊢
  intro ε hε
  simpa [Real.dist_eq, sub_eq_add_neg, abs_sub_comm] using hraw ε hε

/-- **Theorem 7.4 conditional `σ̂²` consistency assembly.**

Once Hansen's two residual-decomposition remainders are known to be `oₚ(1)`,
the centered residual average `σ̂² - σ²` is `oₚ(1)`. The remaining work for the
unconditional Theorem 7.4 statement is to discharge `hcross` and `hquad` from
Theorem 7.1 consistency and the sample-moment WLLNs. -/
theorem olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero_of_remainders
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hcross : TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0))
    (hquad : TendstoInMeasure μ
      (fun n ω =>
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω) -
          errorVariance μ e)
      atTop
      (fun _ => 0) := by
  have herr :=
    sampleErrorSecondMoment_stackErrors_sub_errorVariance_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) h
  have hsum :=
    TendstoInMeasure.add_zero_real
      (TendstoInMeasure.add_zero_real herr hcross) hquad
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  change sampleErrorSecondMoment (stackErrors e n ω) - errorVariance μ e +
        -2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) +
        ((olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) =
      olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω) -
        errorVariance μ e
  rw [olsSigmaSqHatStar_stack_linear_model X e y β hmodel]
  ring

/-- **Theorem 7.4 conditional `σ̂²` consistency.**

This is the uncentered presentation of
`olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero_of_remainders`:
`σ̂² →ₚ σ²`, conditional on the two residual-decomposition remainders being
`oₚ(1)`. -/
theorem olsSigmaSqHatStar_tendstoInMeasure_errorVariance_of_remainders
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hcross : TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0))
    (hquad : TendstoInMeasure μ
      (fun n ω =>
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop
      (fun _ => errorVariance μ e) := by
  have hsub :=
    olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero_of_remainders
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hcross hquad
  rw [tendstoInMeasure_iff_dist] at hsub ⊢
  intro ε hε
  simpa [Real.dist_eq, sub_eq_add_neg, abs_sub_comm] using hsub ε hε

/-- **Core stochastic transform — convergence of the OLS-error term.**
Under the moment-level assumptions, the sequence `Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` — which is the
deterministic RHS of the Phase 1 OLS-error identity `β̂ₙ − β = Q̂ₙ⁻¹ *ᵥ ĝₙ(e)`
(valid on the event `{Q̂ₙ invertible}`) — converges in probability to `0`.

Proof chain:
* Task 9: `Q̂ₙ →ₚ Q`.
* Task 7: composed with Task 9 and `h.Q_nonsing`, this gives `Q̂ₙ⁻¹ →ₚ Q⁻¹`.
* Task 10: `ĝₙ(e) →ₚ 0`.
* `tendstoInMeasure_mulVec` joins these to `Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ Q⁻¹ *ᵥ 0 = 0`.

This theorem is the core stochastic term in the consistency proof below. -/
theorem sampleGramInv_mulVec_sampleCrossMoment_e_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω =>
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => (0 : k → ℝ)) := by
  have hGram := sampleGram_stackRegressors_tendstoInMeasure_popGram h
  have hCross := sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero h
  -- Measurability of sampleGram via (1/n) • ∑ Xᵢ Xᵢᵀ
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hCross_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    intro n
    exact sampleCrossMoment_stackRegressors_stackErrors_aestronglyMeasurable h n
  have hInv : TendstoInMeasure μ
      (fun n ω => (sampleGram (stackRegressors X n ω))⁻¹)
      atTop (fun _ => (popGram μ X)⁻¹) :=
    tendstoInMeasure_matrix_inv hGram_meas hGram (fun _ => h.Q_nonsing)
  have hInv_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hmulVec := tendstoInMeasure_mulVec hInv_meas hCross_meas hInv hCross
  simpa using hmulVec

/-- **Measure of the singular event vanishes asymptotically.**
Under the moment-level assumptions, `μ {ω | Q̂ₙ(ω) is singular} → 0`.

Proof chain:
* Task 9: `Q̂ₙ →ₚ Q`.
* CMT on `Matrix.det` (continuous): `det Q̂ₙ →ₚ det Q`.
* `det Q ≠ 0` by `h.Q_nonsing`, so `ε := |det Q|/2 > 0`.
* On the singular event, `det Q̂ₙ(ω) = 0`, so `edist 0 (det Q) = |det Q| ≥ ε`.
* Monotonicity: `μ {singular} ≤ μ {|det Q̂ₙ − det Q| ≥ ε} → 0`. -/
theorem measure_sampleGram_singular_tendsto_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    Tendsto (fun n => μ {ω | ¬ IsUnit (sampleGram (stackRegressors X n ω)).det})
      atTop (𝓝 0) := by
  have hGram := sampleGram_stackRegressors_tendstoInMeasure_popGram h
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hDet : TendstoInMeasure μ
      (fun n ω => (sampleGram (stackRegressors X n ω)).det)
      atTop (fun _ => (popGram μ X).det) :=
    tendstoInMeasure_continuous_comp hGram_meas hGram
      (Continuous.matrix_det continuous_id)
  have hqne : (popGram μ X).det ≠ 0 := h.Q_nonsing.ne_zero
  set ε : ℝ := |(popGram μ X).det| / 2 with hε_def
  have hε_pos : 0 < ε := half_pos (abs_pos.mpr hqne)
  have hε_le : ε ≤ |(popGram μ X).det| := by
    rw [hε_def]; linarith [abs_nonneg ((popGram μ X).det)]
  have hmeas_eps := hDet (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas_eps
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero, not_not] at hω
  simp only [Set.mem_setOf_eq, hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
  exact ENNReal.ofReal_le_ofReal hε_le

/-- **Residual convergence in probability.** Under the moment-level assumptions and
the linear model `yᵢ = Xᵢ·β + eᵢ`, the residual
`β̂ₙ − β − Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` converges to `0` in probability.

On the event `{Q̂ₙ invertible}`, this residual is identically `0` by
`olsBetaStar_sub_identity` + `nonsing_inv_mul`. The complement event has
vanishing measure by `measure_sampleGram_singular_tendsto_zero` (F4). -/
theorem residual_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
          (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop (fun _ => (0 : k → ℝ)) := by
  have hsingular := measure_sampleGram_singular_tendsto_zero h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  have hR : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) = 0 := by
    rw [olsBetaStar_sub_identity X e y β hmodel,
        Matrix.nonsing_inv_mul _ hunit, sub_self, Matrix.zero_mulVec]
  rw [hR, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- **Scaled residual convergence in probability.** The same high-probability
invertibility argument kills the residual after multiplying by `√n`.

This is the singular-event remainder needed before the feasible OLS CLT can be
assembled: on `{Q̂ₙ invertible}` the residual is exactly zero, while the
singular event still has probability tending to zero. No rate is needed. -/
theorem sqrt_smul_residual_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
      atTop (fun _ => (0 : k → ℝ)) := by
  have hsingular := measure_sampleGram_singular_tendsto_zero h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  have hR : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) = 0 := by
    rw [olsBetaStar_sub_identity X e y β hmodel,
        Matrix.nonsing_inv_mul _ hunit, sub_self, Matrix.zero_mulVec]
  rw [hR, smul_zero, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- **Scalar projection of the scaled residual is negligible.** For every fixed
projection vector `a`, the scalar projection of the singular-event residual is
`oₚ(1)`.

This is the projectionwise form needed by the Cramér-Wold-facing CLT layer. -/
theorem scoreProjection_sqrt_smul_residual_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β a : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  have hsingular := measure_sampleGram_singular_tendsto_zero h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  have hR : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) = 0 := by
    rw [olsBetaStar_sub_identity X e y β hmodel,
        Matrix.nonsing_inv_mul _ hunit, sub_self, Matrix.zero_mulVec]
  rw [hR, smul_zero] at hω
  simp only [zero_dotProduct, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- **Scaled totalized OLS decomposition.**
The centered and scaled total estimator splits into the singular-event residual
plus the feasible leading score term:
`√n(β̂*ₙ - β) = √n·Rₙ + Q̂ₙ⁻¹ *ᵥ (√n·ĝₙ(e))`.

This is pure deterministic algebra. The preceding theorem proves
`√n·Rₙ →ₚ 0`; the remaining Chapter 7 CLT work is to transfer the score CLT
through the random inverse `Q̂ₙ⁻¹`. -/
theorem sqrt_smul_olsBetaStar_sub_eq_sqrt_smul_residual_add_feasible_score
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (n : ℕ) (ω : Ω) :
    Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) =
      Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) := by
  rw [Matrix.mulVec_smul]
  have hsplit : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β =
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) := by
    abel
  calc
    Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
        = Real.sqrt (n : ℝ) •
          ((olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
              (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
                sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) := by
            exact congrArg (fun v : k → ℝ => Real.sqrt (n : ℝ) • v) hsplit
    _ = Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
        Real.sqrt (n : ℝ) •
          ((sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) := by
        rw [smul_add]

/-- **Vector Slutsky residual for totalized OLS.**

The difference between the scaled totalized OLS error and the feasible leading
score `Q̂ₙ⁻¹√nĝₙ(e)` is `oₚ(1)`. This is the vector form needed by Mathlib's
distributional Slutsky theorem. -/
theorem sqrt_smul_olsBetaStar_sub_sub_feasibleScore_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) -
          (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
            (Real.sqrt (n : ℝ) •
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
      atTop (fun _ => (0 : k → ℝ)) := by
  have hres := sqrt_smul_residual_tendstoInMeasure_zero
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  refine hres.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  change
    Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
          (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
      Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) -
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
  rw [Matrix.mulVec_smul, smul_sub]

/-- **Feasible leading-term decomposition.**
The feasible leading score term is the fixed-`Q⁻¹` leading term plus the
random-inverse gap:
`Q̂ₙ⁻¹√nĝₙ(e) = Q⁻¹√nĝₙ(e) + (Q̂ₙ⁻¹ - Q⁻¹)√nĝₙ(e)`.

This names the exact remainder that the remaining Slutsky/tightness argument
must show is negligible. -/
theorem feasibleScore_eq_fixedScore_add_inverseGap
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (n : ℕ) (ω : Ω) :
    (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
      (popGram μ X)⁻¹ *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
        ((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) := by
  rw [Matrix.sub_mulVec]
  abel

/-- **Random-weight form of the inverse-gap projection.**
The scalar inverse-gap term can be viewed as the scaled score projected against
the random weight `(Q̂ₙ⁻¹ - Q⁻¹)ᵀa`.

This is the deterministic algebra behind the remaining tightness/product step:
the weight should converge to zero in probability, while the scaled score is
tight by the CLT. -/
theorem inverseGapProjection_eq_scoreProjection_randomWeight
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (a : k → ℝ) (n : ℕ) (ω : Ω) :
    (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a =
      (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]

/-- **Random inverse-gap weight converges to zero.**
For a fixed projection vector `a`, the random weight
`(Q̂ₙ⁻¹ - Q⁻¹)ᵀa` converges to zero in probability.

This is the deterministic-continuous-mapping half of the inverse-gap product
argument; the other half is boundedness in probability of the scaled score. -/
theorem inverseGapWeight_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (a : k → ℝ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a))
      atTop (fun _ => 0) := by
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv h
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hcont : Continuous
      (fun M : Matrix k k ℝ => (M - (popGram μ X)⁻¹)ᵀ *ᵥ a) := by
    fun_prop
  have hmap := tendstoInMeasure_continuous_comp hInv_meas hInv hcont
  simpa using hmap

/-- Coordinate form of `inverseGapWeight_tendstoInMeasure_zero`. -/
theorem inverseGapWeight_coord_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (a : k → ℝ) (j : k) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a) j)
      atTop (fun _ => 0) := by
  exact TendstoInMeasure.pi_apply (inverseGapWeight_tendstoInMeasure_zero h a) j

/-- **Coordinatewise inverse-gap Slutsky bridge.**
For a fixed projection vector `a`, the inverse-gap projection is `oₚ(1)` once
each coordinate of the random weight `(Q̂ₙ⁻¹ - Q⁻¹)ᵀa` is `oₚ(1)` and each
coordinate of the scaled score `√n·ĝₙ(e)` is `Oₚ(1)`.

This is the product-rule heart of the remaining proof of Hansen Theorem 7.3:
after `inverseGapProjection_eq_scoreProjection_randomWeight`, the inverse gap
is a finite sum of coordinate products. -/
theorem inverseGapProjection_tendstoInMeasure_zero_of_coord
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (a : k → ℝ)
    (hweight : ∀ j : k,
      TendstoInMeasure μ
        (fun (n : ℕ) ω =>
          (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a) j)
        atTop (fun _ => 0))
    (hscoreBounded : ∀ j : k,
      BoundedInProbability μ
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j)) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  let score : ℕ → Ω → k → ℝ := fun n ω =>
    Real.sqrt (n : ℝ) •
      sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)
  let weight : ℕ → Ω → k → ℝ := fun n ω =>
    (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a)
  have hprod : ∀ j ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ (fun n ω => weight n ω j * score n ω j)
        atTop (fun _ => 0) := by
    intro j _
    exact TendstoInMeasure.mul_boundedInProbability
      (by simpa [weight] using hweight j)
      (by simpa [score] using hscoreBounded j)
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun j n ω => weight n ω j * score n ω j) hprod
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  dsimp [score, weight]
  rw [inverseGapProjection_eq_scoreProjection_randomWeight (μ := μ) (X := X) (e := e) a n ω]
  simp [dotProduct, mul_comm]

/-- **Inverse-gap projection from scaled-score boundedness.**
For a fixed projection vector `a`, the inverse-gap projection is `oₚ(1)` once
each coordinate of the scaled score `√n·ĝₙ(e)` is `Oₚ(1)`.

The random-weight side is now discharged by
`inverseGapWeight_coord_tendstoInMeasure_zero`; the remaining theorem-facing
task is supplying score boundedness, which `SampleCLTAssumption72` later
provides via the scalar score CLT. -/
theorem inverseGapProjection_tendstoInMeasure_zero_of_scoreBounded
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (a : k → ℝ)
    (hscoreBounded : ∀ j : k,
      BoundedInProbability μ
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j)) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  exact inverseGapProjection_tendstoInMeasure_zero_of_coord a
    (fun j => inverseGapWeight_coord_tendstoInMeasure_zero h a j)
    hscoreBounded

/-- **Scalar-projection decomposition for the totalized OLS CLT.**
For every fixed projection vector `a`, the scaled totalized OLS error decomposes
into:

1. the scaled singular-event residual projection,
2. the fixed-`Q⁻¹` score projection with the known scalar CLT,
3. the random-inverse gap projection still left for Slutsky/tightness.

This is the exact algebraic roadmap for the remaining proof of Hansen's
Theorem 7.3. -/
theorem scoreProjection_sqrt_smul_olsBetaStar_sub_eq_residual_add_fixedScore_add_inverseGap
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {y : ℕ → Ω → ℝ} (β a : k → ℝ) (n : ℕ) (ω : Ω) :
    (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a =
      (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a +
        (Real.sqrt (n : ℝ) •
          ((popGram μ X)⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a +
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a := by
  rw [sqrt_smul_olsBetaStar_sub_eq_sqrt_smul_residual_add_feasible_score,
      feasibleScore_eq_fixedScore_add_inverseGap (μ := μ), Matrix.mulVec_smul,
      add_dotProduct, add_dotProduct]
  ring

/-- **Scalar Slutsky remainder from the inverse gap.**
For a fixed projection vector `a`, the difference between the scaled totalized
OLS projection and the fixed-`Q⁻¹` score projection is `oₚ(1)` once the
random-inverse gap projection is `oₚ(1)`.

The scaled residual part is already controlled by
`scoreProjection_sqrt_smul_residual_tendstoInMeasure_zero`; this theorem makes
the remaining target exactly the inverse-gap/tightness step. -/
theorem scoreProjection_olsBetaStar_remainder_tendstoInMeasure_zero_of_inverseGap
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β a : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hinvGap : TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a -
          (Real.sqrt (n : ℝ) •
            ((popGram μ X)⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  let residual : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt (n : ℝ) •
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a
  let gap : ℕ → Ω → ℝ := fun n ω =>
    (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
      (Real.sqrt (n : ℝ) •
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a
  have hresConv : TendstoInMeasure μ residual atTop (fun _ => 0) := by
    simpa [residual] using
      scoreProjection_sqrt_smul_residual_tendstoInMeasure_zero β a h hmodel
  have hgapConv : TendstoInMeasure μ gap atTop (fun _ => 0) := by
    simpa [gap] using hinvGap
  have hsumConv : TendstoInMeasure μ (fun n ω => residual n ω + gap n ω)
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist] at hresConv hgapConv ⊢
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hsum := (hresConv (ε / 2) hε2).add (hgapConv (ε / 2) hε2)
    have hsum0 : Tendsto
        (fun (n : ℕ) =>
          μ {ω | ε / 2 ≤ dist (residual n ω) 0} +
          μ {ω | ε / 2 ≤ dist (gap n ω) 0})
        atTop (𝓝 0) := by
      simpa using hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum0
      (fun _ => zero_le _) (fun n => ?_)
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_cases hres_big : ε / 2 ≤ dist (residual n ω) 0
    · exact Or.inl hres_big
    · right
      by_contra hgap_small_not
      have hres_small : dist (residual n ω) 0 < ε / 2 := not_le.mp hres_big
      have hgap_small : dist (gap n ω) 0 < ε / 2 := not_le.mp hgap_small_not
      have htri : dist (residual n ω + gap n ω) 0 ≤
          dist (residual n ω) 0 + dist (gap n ω) 0 := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq]
        simpa using abs_add_le (residual n ω) (gap n ω)
      have hlt : dist (residual n ω + gap n ω) 0 < ε := by linarith
      exact (not_le.mpr hlt) hω
  refine hsumConv.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  dsimp [residual, gap]
  rw [scoreProjection_sqrt_smul_olsBetaStar_sub_eq_residual_add_fixedScore_add_inverseGap]
  ring

/-- **Consistency of the totalized least-squares estimator.**
Under the moment-level assumptions above and the linear model `yᵢ = Xᵢ·β + eᵢ`,
the total OLS estimator `β̂*ₙ := (Xᵀ X)⁺ Xᵀ y` (using `Matrix.nonsingInv`)
converges in probability to `β`.

Proof chain:
* F2: `β̂*ₙ = Q̂ₙ⁻¹ *ᵥ ĝₙ(y)` pointwise.
* F3: `ĝₙ(y) = Q̂ₙ β + ĝₙ(e)` under the linear model.
* F6: residual `β̂*ₙ − β − Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0` (it vanishes on the invertibility
  event, whose complement has measure → 0 by F4).
* Task 11: `Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0`.
* F5 (twice): residual + error term + β →ₚ 0 + 0 + β = β.
* Pointwise algebra: the sum equals `β̂*ₙ`. -/
theorem olsBetaStar_stack_tendstoInMeasure_beta
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : LeastSquaresConsistencyConditions μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => β) := by
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hCrossE_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    intro n
    have hform : (fun ω => sampleCrossMoment (stackRegressors X n ω)
          (stackErrors e n ω)) =
        (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω) := by
      funext ω
      rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
          sum_fin_eq_sum_range_smul]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_cross i).integrable_iff.mpr h.int_cross).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hCoreMV_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    intro n
    have hprod := (hInv_meas n).prodMk (hCrossE_meas n)
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable hprod
  have hR'_meas : ∀ n, AEStronglyMeasurable
      (fun ω => ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β) μ := by
    intro n
    have hmat_mul : AEStronglyMeasurable
        (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω)) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        ((hInv_meas n).prodMk (hGram_meas n))
    have hmat_sub : AEStronglyMeasurable
        (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) μ :=
      hmat_mul.sub aestronglyMeasurable_const
    exact (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      hmat_sub
  -- R'_n →ₚ 0 via F6 + the residual identity
  have hF6 := residual_tendstoInMeasure_zero β h hmodel
  have hR' : TendstoInMeasure μ
      (fun n ω => ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β)
      atTop (fun _ => (0 : k → ℝ)) :=
    hF6.congr_left (fun n => ae_of_all μ (fun ω =>
      olsBetaStar_sub_identity X e y β hmodel n ω))
  -- Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0 (Task 11)
  have hCore := sampleGramInv_mulVec_sampleCrossMoment_e_tendstoInMeasure_zero h
  -- R'_n + Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0
  have hSum := tendstoInMeasure_add hR'_meas hCoreMV_meas hR' hCore
  simp only [add_zero] at hSum
  -- (R'_n + Q̂ₙ⁻¹ *ᵥ ĝₙ(e)) + β →ₚ β
  have hConst : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => β) atTop (fun _ => β) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  have hSumPlus := tendstoInMeasure_add
    (fun n => (hR'_meas n).add (hCoreMV_meas n))
    (fun _ => aestronglyMeasurable_const)
    hSum hConst
  simp only [zero_add] at hSumPlus
  -- Congr to olsBetaStar via the residual identity
  refine hSumPlus.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  simp only [Pi.add_apply]
  have hident := olsBetaStar_sub_identity X e y β hmodel n ω
  rw [← hident]; abel

/-- **AEMeasurability of the totalized OLS estimator.**

Under the moment assumptions and pointwise linear model, each stacked
`olsBetaStar` random vector is a.e. strongly measurable. This is the
measurability input needed to apply continuous-mapping theorems directly to
functions of `β̂*ₙ`. -/
theorem olsBetaStar_stack_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    ∀ n, AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hCrossE_meas : AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    have hform : (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
        (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω) := by
      funext ω
      rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
          sum_fin_eq_sum_range_smul]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_cross i).integrable_iff.mpr h.int_cross).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram_meas
  have hGramBeta_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω) *ᵥ β) μ :=
    (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      hGram_meas
  have hMiddle_meas : AEStronglyMeasurable
      (fun ω =>
        sampleGram (stackRegressors X n ω) *ᵥ β +
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ :=
    hGramBeta_meas.add hCrossE_meas
  have hRhs_meas : AEStronglyMeasurable
      (fun ω =>
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ β +
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) μ := by
    have hprod := hInv_meas.prodMk hMiddle_meas
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable hprod
  refine hRhs_meas.congr (ae_of_all μ (fun ω => ?_))
  change
    (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        (sampleGram (stackRegressors X n ω) *ᵥ β +
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
      olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)
  rw [← sampleCrossMoment_stackOutcomes_linear_model X e y β hmodel,
      ← olsBetaStar_stack_eq_sampleGramInv_mulVec_sampleCrossMoment X y n ω]

/-- **Hansen Theorem 7.8, continuous functions of totalized OLS.**

For any globally continuous parameter transform `φ`, consistency of the
totalized OLS estimator transfers to `φ(β̂*ₙ) →ₚ φ(β)`. This is the direct
continuous-mapping-theorem face of Hansen's functions-of-parameters section;
the local-at-`β` formulation below removes the global-continuity requirement. -/
theorem continuous_function_olsBetaStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {F : Type*} [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    (φ : (k → ℝ) → F) (hφ : Continuous φ) :
    TendstoInMeasure μ
      (fun n ω => φ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)))
      atTop (fun _ => φ β) := by
  exact tendstoInMeasure_continuous_comp
    (olsBetaStar_stack_aestronglyMeasurable
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel)
    (olsBetaStar_stack_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel)
    hφ

/-- **Hansen Theorem 7.8, functions continuous at the true value.**

The textbook only requires the parameter transform `φ` to be continuous at the
true value `β`. We keep measurability of the composed sample transform explicit,
because pointwise continuity at `β` alone is not a global measurability
assumption on `φ`. -/
theorem continuousAt_function_olsBetaStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {F : Type*} [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    (φ : (k → ℝ) → F) (hφ : ContinuousAt φ β)
    (hφ_meas : ∀ n, AEStronglyMeasurable
      (fun ω => φ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))) μ) :
    TendstoInMeasure μ
      (fun n ω => φ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)))
      atTop (fun _ => φ β) := by
  exact tendstoInMeasure_continuousAt_const_comp
    (olsBetaStar_stack_aestronglyMeasurable
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel)
    hφ_meas
    (olsBetaStar_stack_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel)
    hφ

/-- **Hansen Theorem 7.8 for ordinary OLS on nonsingular samples.**

The same continuous-function consistency statement holds for `olsBetaOrZero`,
the wrapper that agrees with ordinary OLS on nonsingular samples and with
`olsBetaStar` unconditionally. -/
theorem continuous_function_olsBetaOrZero_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {F : Type*} [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    (φ : (k → ℝ) → F) (hφ : Continuous φ) :
    TendstoInMeasure μ
      (fun n ω => φ (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)))
      atTop (fun _ => φ β) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    continuous_function_olsBetaStar_tendstoInMeasure
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel φ hφ

/-- **Theorem 7.1 ordinary-OLS-on-nonsingular-samples consistency.**

The textbook-facing wrapper `olsBetaOrZero` equals ordinary `olsBeta` whenever
the sample Gram is nonsingular and equals `olsBetaStar` unconditionally, so the
totalized consistency theorem transfers directly. -/
theorem olsBetaOrZero_stack_tendstoInMeasure_beta
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : LeastSquaresConsistencyConditions μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => β) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsBetaStar_stack_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel

/-- AEMeasurability of the ordinary-on-nonsingular OLS wrapper. -/
theorem olsBetaOrZero_stack_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    ∀ n, AEStronglyMeasurable
      (fun ω => olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  refine (olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel n).congr ?_
  exact ae_of_all μ (fun ω => (olsBetaOrZero_eq_olsBetaStar
    (stackRegressors X n ω) (stackOutcomes y n ω)).symm)

/-- **Hansen Theorem 7.8 for ordinary OLS, local-at-`β` formulation.**

This is the ordinary-wrapper counterpart of
`continuousAt_function_olsBetaStar_tendstoInMeasure`: a transform continuous at
the true value preserves consistency, with measurability of the composed sample
transform kept explicit. -/
theorem continuousAt_function_olsBetaOrZero_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {F : Type*} [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    (φ : (k → ℝ) → F) (hφ : ContinuousAt φ β)
    (hφ_meas : ∀ n, AEStronglyMeasurable
      (fun ω => φ (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω))) μ) :
    TendstoInMeasure μ
      (fun n ω => φ (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)))
      atTop (fun _ => φ β) := by
  exact tendstoInMeasure_continuousAt_const_comp
    (olsBetaOrZero_stack_aestronglyMeasurable
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel)
    hφ_meas
    (olsBetaOrZero_stack_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel)
    hφ

/-- **Theorem 7.4 cross remainder.**

The cross term in the residual-variance expansion is negligible:
`-2 ĝₙ(e)'(β̂*ₙ - β) = oₚ(1)`. It follows coordinatewise from the sample
cross-moment WLLN, Theorem 7.1 consistency, and the finite dot-product
`oₚ(1)·oₚ(1)` rule. -/
theorem olsSigmaSqHatStar_crossRemainder_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0) := by
  have hCross :=
    sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71
  have hBeta :=
    olsBetaStar_stack_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (y := y) β
      h.toSampleMomentAssumption71 hmodel
  have hCrossCoord : ∀ j : k,
      TendstoInMeasure μ
        (fun n ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) j)
        atTop (fun _ => 0) := by
    intro j
    exact TendstoInMeasure.pi_apply hCross j
  have hBetaCoord : ∀ j : k,
      TendstoInMeasure μ
        (fun n ω =>
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) j)
        atTop (fun _ => 0) := by
    intro j
    have hj := TendstoInMeasure.pi_apply hBeta j
    have hcenter := TendstoInMeasure.sub_limit_zero_real hj
    simpa [Pi.sub_apply] using hcenter
  have hdot := tendstoInMeasure_dotProduct_zero_real (μ := μ)
    (X := fun n ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
    (Y := fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
    hCrossCoord hBetaCoord
  simpa using TendstoInMeasure.const_mul_zero_real (μ := μ) (-2) hdot

/-- **Theorem 7.4 Gram-weighted estimation error.**

The sample Gram times the estimation error is negligible:
`Q̂ₙ(β̂*ₙ - β) = oₚ(1)`. The proof is coordinatewise: each summand is
`Q̂ₙ,jl dₙ,l = (Q̂ₙ,jl - Q_jl)dₙ,l + Q_jl dₙ,l`, with both terms `oₚ(1)`. -/
theorem sampleGram_mulVec_olsBetaStar_sub_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleGram (stackRegressors X n ω) *ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0) := by
  let Qhat : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleGram (stackRegressors X n ω)
  let d : ℕ → Ω → k → ℝ := fun n ω =>
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β
  have hGram := sampleGram_stackRegressors_tendstoInMeasure_popGram
    (μ := μ) (X := X) (e := e) h
  have hBeta := olsBetaStar_stack_tendstoInMeasure_beta
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  have hDiffCoord : ∀ l : k,
      TendstoInMeasure μ (fun n ω => d n ω l) atTop (fun _ => 0) := by
    intro l
    have hl := TendstoInMeasure.pi_apply hBeta l
    have hcenter := TendstoInMeasure.sub_limit_zero_real hl
    simpa [d, Pi.sub_apply] using hcenter
  have hGramCoord : ∀ j l : k,
      TendstoInMeasure μ (fun n ω => Qhat n ω j l)
        atTop (fun _ => (popGram μ X) j l) := by
    intro j l
    exact TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hGram j) l
  have hCoord : ∀ j : k,
      TendstoInMeasure μ (fun n ω => (Qhat n ω *ᵥ d n ω) j)
        atTop (fun _ => 0) := by
    intro j
    have hterm : ∀ l ∈ (Finset.univ : Finset k),
        TendstoInMeasure μ (fun n ω => Qhat n ω j l * d n ω l)
          atTop (fun _ => 0) := by
      intro l _
      have hQcenter := TendstoInMeasure.sub_limit_zero_real (hGramCoord j l)
      have hcenterProd := TendstoInMeasure.mul_zero_real hQcenter (hDiffCoord l)
      have hconstProd := TendstoInMeasure.const_mul_zero_real
        (μ := μ) ((popGram μ X) j l) (hDiffCoord l)
      have hsum := TendstoInMeasure.add_zero_real hcenterProd hconstProd
      refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
      dsimp [Qhat, d]
      ring
    have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset k))
      (X := fun l n ω => Qhat n ω j l * d n ω l) hterm
    refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    simp [Qhat, d, Matrix.mulVec, dotProduct]
  simpa [Qhat, d] using tendstoInMeasure_pi (μ := μ) hCoord

/-- **Theorem 7.4 quadratic remainder.**

The quadratic term in the residual-variance expansion is negligible:
`(β̂*ₙ - β)'Q̂ₙ(β̂*ₙ - β) = oₚ(1)`. -/
theorem olsSigmaSqHatStar_quadraticRemainder_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0) := by
  let d : ℕ → Ω → k → ℝ := fun n ω =>
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β
  let Qd : ℕ → Ω → k → ℝ := fun n ω =>
    sampleGram (stackRegressors X n ω) *ᵥ d n ω
  have hBeta := olsBetaStar_stack_tendstoInMeasure_beta
    (μ := μ) (X := X) (e := e) (y := y) β
    h.toSampleMomentAssumption71 hmodel
  have hDiffCoord : ∀ j : k,
      TendstoInMeasure μ (fun n ω => d n ω j) atTop (fun _ => 0) := by
    intro j
    have hj := TendstoInMeasure.pi_apply hBeta j
    have hcenter := TendstoInMeasure.sub_limit_zero_real hj
    simpa [d, Pi.sub_apply] using hcenter
  have hQd := sampleGram_mulVec_olsBetaStar_sub_tendstoInMeasure_zero
    (μ := μ) (X := X) (e := e) (y := y)
    h.toSampleMomentAssumption71 β hmodel
  have hQdCoord : ∀ j : k,
      TendstoInMeasure μ (fun n ω => Qd n ω j) atTop (fun _ => 0) := by
    intro j
    simpa [Qd, d] using TendstoInMeasure.pi_apply hQd j
  have hdot := tendstoInMeasure_dotProduct_zero_real (μ := μ)
    (X := d) (Y := Qd) hDiffCoord hQdCoord
  simpa [d, Qd] using hdot

/-- **Theorem 7.4 centered residual-variance consistency.**

Under the squared-error WLLN assumptions and the linear model,
`σ̂²ₙ - σ² = oₚ(1)` for the totalized OLS residual average. -/
theorem olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω) -
          errorVariance μ e)
      atTop (fun _ => 0) := by
  exact olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero_of_remainders
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
    (olsSigmaSqHatStar_crossRemainder_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)
    (olsSigmaSqHatStar_quadraticRemainder_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)

/-- **Theorem 7.4 residual-variance consistency.**

Under the squared-error WLLN assumptions and the linear model, the totalized
OLS residual average `σ̂²ₙ` converges in probability to `σ² = E[e₀²]`. -/
theorem olsSigmaSqHatStar_tendstoInMeasure_errorVariance
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop
      (fun _ => errorVariance μ e) := by
  exact olsSigmaSqHatStar_tendstoInMeasure_errorVariance_of_remainders
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
    (olsSigmaSqHatStar_crossRemainder_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)
    (olsSigmaSqHatStar_quadraticRemainder_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)

/-- **Theorem 7.4 centered degrees-of-freedom variance consistency.**

The degrees-of-freedom adjusted totalized residual variance satisfies
`s²ₙ - σ² = oₚ(1)`. -/
theorem olsS2Star_sub_errorVariance_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        olsS2Star (stackRegressors X n ω) (stackOutcomes y n ω) -
          errorVariance μ e)
      atTop (fun _ => 0) := by
  let r : ℕ → ℝ := fun n =>
    (n : ℝ) * ((n : ℝ) - (Fintype.card k : ℝ))⁻¹
  let sigmaHat : ℕ → Ω → ℝ := fun n ω =>
    olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω)
  have hSigmaCentered :=
    olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto
      (fun n : ℕ => (n : ℝ) - (Fintype.card k : ℝ)) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(Fintype.card k : ℝ)) hn
  have hrSub : Tendsto (fun n => r n - 1) atTop (𝓝 0) := by
    have hsmall : Tendsto
        (fun n : ℕ => (Fintype.card k : ℝ) /
          ((n : ℝ) - (Fintype.card k : ℝ))) atTop (𝓝 0) :=
      hden.const_div_atTop (Fintype.card k : ℝ)
    have heq : (fun n => r n - 1) =ᶠ[atTop]
        (fun n : ℕ => (Fintype.card k : ℝ) /
          ((n : ℝ) - (Fintype.card k : ℝ))) := by
      filter_upwards [eventually_gt_atTop (Fintype.card k)] with n hn_gt
      have hden_ne : (n : ℝ) - (Fintype.card k : ℝ) ≠ 0 := by
        have hgt : (Fintype.card k : ℝ) < (n : ℝ) := by
          exact_mod_cast hn_gt
        linarith
      dsimp [r]
      field_simp [hden_ne]
      ring
    rw [tendsto_congr' heq]
    exact hsmall
  have hr : Tendsto r atTop (𝓝 1) := by
    have hadd := hrSub.add_const 1
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd
  have hbound : ∀ᶠ n in atTop, |r n| ≤ 2 := by
    have hnear : ∀ᶠ n in atTop, dist (r n) 1 < 1 :=
      eventually_atTop.2 ((Metric.tendsto_atTop.1 hr) 1 one_pos)
    filter_upwards [hnear] with n hn_near
    have habs : |r n - 1| < 1 := by
      simpa [Real.dist_eq] using hn_near
    have hleft := (abs_lt.mp habs).1
    have hright := (abs_lt.mp habs).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hscaledCentered : TendstoInMeasure μ
      (fun n ω => r n * (sigmaHat n ω - errorVariance μ e))
      atTop (fun _ => 0) := by
    exact TendstoInMeasure.mul_deterministic_bounded_zero_real
      (μ := μ) (M := 2) (by norm_num) hbound
      (by simpa [sigmaHat] using hSigmaCentered)
  have hdetReal : Tendsto
      (fun n => (r n - 1) * errorVariance μ e) atTop (𝓝 0) := by
    simpa using hrSub.mul tendsto_const_nhds
  have hdetMeasure : TendstoInMeasure μ
      (fun n (_ : Ω) => (r n - 1) * errorVariance μ e)
      atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) hdetReal
  have hscaled :=
    TendstoInMeasure.add_zero_real hscaledCentered hdetMeasure
  have hcenter : TendstoInMeasure μ
      (fun n ω => r n * sigmaHat n ω - errorVariance μ e)
      atTop (fun _ => 0) := by
    refine hscaled.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    ring
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hcenter
  filter_upwards [eventually_gt_atTop 0] with n hn_pos
  exact ae_of_all μ (fun ω => by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
    dsimp [r, sigmaHat]
    rw [olsS2Star_eq_card_div_df_mul_olsSigmaSqHatStar]
    simp [Fintype.card_fin, div_eq_mul_inv])

/-- **Theorem 7.4 degrees-of-freedom variance consistency.**

Under the squared-error WLLN assumptions and the linear model, the
degrees-of-freedom adjusted totalized residual variance `s²ₙ` converges in
probability to `σ² = E[e₀²]`. -/
theorem olsS2Star_tendstoInMeasure_errorVariance
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsS2Star (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop
      (fun _ => errorVariance μ e) := by
  exact TendstoInMeasure.of_sub_limit_zero_real
    (olsS2Star_sub_errorVariance_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)

/-- Hansen's homoskedastic asymptotic covariance matrix
`V⁰_β := σ² Q⁻¹`. -/
noncomputable def homoskedasticAsymptoticCovariance
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  errorVariance μ e • (popGram μ X)⁻¹

/-- The totalized plug-in estimator `V̂⁰_β := s² Q̂⁻¹` for Hansen Theorem 7.5. -/
noncomputable def olsHomoskedasticCovarianceStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  olsS2Star X y • (sampleGram X)⁻¹

/-- **Hansen Theorem 7.5, totalized homoskedastic covariance consistency.**

Under the variance-estimator assumptions and the linear model, the plug-in
homoskedastic covariance estimator `V̂⁰_β = s² Q̂⁻¹` converges in probability to
`V⁰_β = σ² Q⁻¹`. -/
theorem olsHomoskedasticCovarianceStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => homoskedasticAsymptoticCovariance μ X e) := by
  let s2 : ℕ → Ω → ℝ := fun n ω =>
    olsS2Star (stackRegressors X n ω) (stackOutcomes y n ω)
  let invGram : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  have hs2 := olsS2Star_tendstoInMeasure_errorVariance
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71
  have hEntry : ∀ i j : k,
      TendstoInMeasure μ
        (fun n ω => s2 n ω * invGram n ω i j)
        atTop
        (fun _ => errorVariance μ e * ((popGram μ X)⁻¹) i j) := by
    intro i j
    have hInvCoord : TendstoInMeasure μ
        (fun n ω => invGram n ω i j)
        atTop (fun _ => ((popGram μ X)⁻¹) i j) := by
      simpa [invGram] using
        TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hInv i) j
    exact TendstoInMeasure.mul_limits_real
      (by simpa [s2] using hs2) hInvCoord
  refine tendstoInMeasure_pi (μ := μ) (fun i => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun j => ?_)
  simpa [olsHomoskedasticCovarianceStar, homoskedasticAsymptoticCovariance,
    s2, invGram, Pi.smul_apply, smul_eq_mul] using hEntry i j

/-- AEMeasurability of the totalized homoskedastic covariance estimator from
component measurability. -/
theorem olsHomoskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hBeta_meas := olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel n
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram_meas
  have hdot_fixed_cont : Continuous (fun x : k → ℝ => x ⬝ᵥ β) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ => (continuous_apply i).mul continuous_const))
  have hdot_pair_cont : Continuous (fun p : (k → ℝ) × (k → ℝ) => p.1 ⬝ᵥ p.2) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ =>
          ((continuous_apply i).comp continuous_fst).mul
            ((continuous_apply i).comp continuous_snd)))
  have hres : ∀ i : Fin n, AEStronglyMeasurable
      (fun ω =>
        olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) μ := by
    intro i
    have hXrow : AEStronglyMeasurable (fun ω => stackRegressors X n ω i) μ := by
      simpa [stackRegressors] using hX_meas i.val
    have hYrow : AEStronglyMeasurable (fun ω => stackOutcomes y n ω i) μ := by
      have hYexpr : AEStronglyMeasurable
          (fun ω => X i.val ω ⬝ᵥ β + e i.val ω) μ :=
        (hdot_fixed_cont.comp_aestronglyMeasurable (hX_meas i.val)).add (he_meas i.val)
      refine hYexpr.congr (ae_of_all μ (fun ω => ?_))
      simpa [stackOutcomes] using (hmodel i.val ω).symm
    have hfit : AEStronglyMeasurable
        (fun ω =>
          stackRegressors X n ω i ⬝ᵥ
            olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hdot_pair_cont.comp_aestronglyMeasurable (hXrow.prodMk hBeta_meas)
    have hres_exp : AEStronglyMeasurable
        (fun ω =>
          stackOutcomes y n ω i -
            stackRegressors X n ω i ⬝ᵥ
              olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hYrow.sub hfit
    refine hres_exp.congr (ae_of_all μ (fun ω => ?_))
    simp [olsResidualStar, Matrix.mulVec, dotProduct]
  have hss : AEStronglyMeasurable
      (fun ω =>
        dotProduct
          (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω))
          (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω))) μ := by
    simpa [dotProduct] using
      Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun i _ => (hres i).mul (hres i))
  have hs2 : AEStronglyMeasurable
      (fun ω =>
        olsS2Star (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
    simpa [olsS2Star] using
      hss.const_mul (((Fintype.card (Fin n) : ℝ) - Fintype.card k)⁻¹)
  simpa [olsHomoskedasticCovarianceStar] using hs2.smul hInv_meas

/-- **AEMeasurability of the scaled totalized-OLS projection.**

The final random variable in the scalar OLS CLT is measurable under the
sample-moment hypotheses and the pointwise linear model. The proof avoids a
standalone measurability theorem for `olsBetaStar` by rewriting
`olsBetaStar - β` with `olsBetaStar_sub_identity` into the measurable
sample-Gram and sample-score pieces. -/
theorem scoreProjection_sqrt_smul_olsBetaStar_sub_aemeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ := by
  intro n
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hCrossE_meas : AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    have hform : (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
        (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω) := by
      funext ω
      rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
          sum_fin_eq_sum_range_smul]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_cross i).integrable_iff.mpr h.int_cross).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram_meas
  have hCoreMV_meas : AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    have hprod := hInv_meas.prodMk hCrossE_meas
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable hprod
  have hR'_meas : AEStronglyMeasurable
      (fun ω => ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β) μ := by
    have hmat_mul : AEStronglyMeasurable
        (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω)) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hInv_meas.prodMk hGram_meas)
    have hmat_sub : AEStronglyMeasurable
        (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) μ :=
      hmat_mul.sub aestronglyMeasurable_const
    exact (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      hmat_sub
  have hvec_meas : AEStronglyMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (((sampleGram (stackRegressors X n ω))⁻¹ *
              sampleGram (stackRegressors X n ω) - 1) *ᵥ β +
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) μ :=
    AEStronglyMeasurable.const_smul (hR'_meas.add hCoreMV_meas) (Real.sqrt (n : ℝ))
  have hdot_cont : Continuous (fun v : k → ℝ => v ⬝ᵥ a) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ => (continuous_apply i).mul continuous_const))
  have hproj_meas : AEStronglyMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (((sampleGram (stackRegressors X n ω))⁻¹ *
              sampleGram (stackRegressors X n ω) - 1) *ᵥ β +
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a) μ :=
    hdot_cont.comp_aestronglyMeasurable hvec_meas
  refine hproj_meas.aemeasurable.congr (ae_of_all μ (fun ω => ?_))
  have hvec : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β =
      ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β +
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) := by
    have hident := olsBetaStar_sub_identity X e y β hmodel n ω
    rw [← hident]
    abel
  exact congrArg (fun v : k → ℝ => (Real.sqrt (n : ℝ) • v) ⬝ᵥ a) hvec.symm

end Assumption71

end HansenEconometrics
