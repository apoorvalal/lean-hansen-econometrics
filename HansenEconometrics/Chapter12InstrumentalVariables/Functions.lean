import HansenEconometrics.ChiSquared
import HansenEconometrics.AsymptoticUtils.DeltaMethod
import HansenEconometrics.Chapter7Asymptotics.SandwichAssembly
import HansenEconometrics.Chapter9HypothesisTesting
import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics

/-!
# Chapter 12 — functions of 2SLS parameters

This file contains the function-of-parameter and Wald-test notation for Hansen
Chapter 12.20--12.21. It reuses the generic Chapter 7/9 delta-method and Wald
machinery rather than duplicating those proofs for IV.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory
  ProbabilityTheory ENNReal

namespace HansenEconometrics

open Matrix

variable {n k l q : Type*}
variable [Fintype n] [Fintype k] [Fintype l] [Fintype q]
variable [DecidableEq k] [DecidableEq l]

omit [Fintype n] [Fintype k] [Fintype l] [Fintype q] [DecidableEq k] [DecidableEq l] in
@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurableSpace (Matrix ι κ ℝ) :=
  matrixBorelMeasurableSpace ι κ

omit [Fintype n] [Fintype k] [Fintype l] [Fintype q] [DecidableEq k] [DecidableEq l] in
private lemma matrixBorelSpaceInst
    (ι κ : Type*) [Fintype ι] [Fintype κ] :
    @BorelSpace (Matrix ι κ ℝ) _ (matrixBorelMeasurableSpaceInst (ι := ι) (κ := κ)) :=
  matrixBorelSpace ι κ

attribute [local instance] matrixBorelMeasurableSpaceInst matrixBorelSpaceInst

/-- Hansen Section 12.20: plug a 2SLS coefficient estimate into a function
`r(β)`. -/
noncomputable def twoSLSFunctionEstimator
    (rfun : (k → ℝ) → (q → ℝ))
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) : q → ℝ :=
  rfun (twoSLSBetaStar Z X Y)

/-- Textbook-facing OrZero version of Hansen Section 12.20's function
estimator `r(β̂₂ₛₗₛ)`. -/
noncomputable def twoSLSFunctionEstimatorOrZero
    (rfun : (k → ℝ) → (q → ℝ))
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) : q → ℝ :=
  rfun (twoSLSBetaOrZero Z X Y)

omit [Fintype q] in
@[simp]
theorem twoSLSFunctionEstimatorOrZero_eq_star
    (rfun : (k → ℝ) → (q → ℝ))
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSFunctionEstimatorOrZero rfun Z X Y =
      twoSLSFunctionEstimator rfun Z X Y := by
  simp [twoSLSFunctionEstimatorOrZero, twoSLSFunctionEstimator]

/-- Hansen Theorem 12.5 covariance transform `V_θ = R' V_β R`, where `R` is
the transpose-oriented derivative matrix used in the chapter. -/
noncomputable def twoSLSFunctionVariance
    (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ) : Matrix q q ℝ :=
  Rᵀ * Vβ * R

/-- Hansen plug-in covariance transform `V̂_θ = R̂' V̂_β R̂`. -/
noncomputable def twoSLSFunctionVHat
    (Vhatβ : Matrix k k ℝ) (Rhat : Matrix k q ℝ) : Matrix q q ℝ :=
  Rhatᵀ * Vhatβ * Rhat

omit [DecidableEq k] in
/-- Positive-definite coefficient covariance and full-column-rank derivative
matrix imply the Hansen Theorem 12.6 function covariance is positive
definite. This is the Chapter 12 notation wrapper around Chapter 8's
restriction-covariance result. -/
theorem twoSLSFunctionVariance_posDef_of_cov_posDef
    (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hVβ : Vβ.PosDef) (hR : Function.Injective R.mulVec) :
    (twoSLSFunctionVariance Vβ R).PosDef := by
  simpa [twoSLSFunctionVariance] using
    restrictionCov_posDef_of_cov_posDef Vβ R hVβ hR

/-- Hansen's positive-definite `Ω`, positive-definite `Q_ZZ`, and full-column-rank
`Q_ZX` imply that the displayed robust 2SLS coefficient covariance is positive
definite. -/
theorem twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ)
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ : QZZ.PosDef)
    (hOmega : Omega.PosDef)
    (hQZX : Function.Injective QZX.mulVec) :
    (twoSLSAsymptoticVariance QXZ QZZ Omega QZX).PosDef := by
  have hQZX_t : QZX = QXZᵀ := by
    rw [hQXZ, Matrix.transpose_transpose]
  rw [twoSLSAsymptoticVariance_eq_linearization_covariance
    (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
    hQZZ.1.eq hQZX_t]
  let B : Matrix k k ℝ := twoSLSBread QXZ QZZ QZX
  let A : Matrix k l ℝ := twoSLSPopulationLinearizationMatrix QXZ QZZ QZX
  have hB_pos : B.PosDef := by
    simpa [B] using twoSLSBread_posDef_of_qzz_posDef_rank hQXZ hQZZ hQZX
  have hQZZ_inv_inj : Function.Injective (QZZ⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 hQZZ.inv.isUnit
  have hB_inv_inj : Function.Injective (B⁻¹).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 hB_pos.inv.isUnit
  have hcomp : Function.Injective
      (fun x : k → ℝ => QZZ⁻¹ *ᵥ (QZX *ᵥ (B⁻¹ *ᵥ x))) :=
    hQZZ_inv_inj.comp (hQZX.comp hB_inv_inj)
  have hQZZ_symm : QZZᵀ = QZZ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hQZZ.1.eq
  have hQZZ_inv_symm : (QZZ⁻¹)ᵀ = QZZ⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hQZZ_symm]
  have hB_symm : Bᵀ = B := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hB_pos.1.eq
  have hB_inv_symm : (B⁻¹)ᵀ = B⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hB_symm]
  have hB_inv_symm' : ((twoSLSBread QXZ QZZ QZX)⁻¹)ᵀ =
      (twoSLSBread QXZ QZZ QZX)⁻¹ := by
    simpa [B] using hB_inv_symm
  have hB_inv_symm_qzx : ((twoSLSBread QZXᵀ QZZ QZX)⁻¹)ᵀ =
      (twoSLSBread QZXᵀ QZZ QZX)⁻¹ := by
    simpa [hQXZ] using hB_inv_symm'
  have hA_trans : Aᵀ = QZZ⁻¹ * QZX * B⁻¹ := by
    simp [A, B, twoSLSPopulationLinearizationMatrix, Matrix.transpose_mul,
      hQZZ_inv_symm, hB_inv_symm_qzx, hQXZ, Matrix.mul_assoc]
  have hA_trans_inj : Function.Injective (Aᵀ).mulVec := by
    rw [hA_trans]
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hcomp
  simpa [A, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hOmega.conjTranspose_mul_mul_same (B := Aᵀ) hA_trans_inj

/-- Hansen Section 12.21 Wald statistic for a nonlinear 2SLS restriction.

The input `root` is the sample normalization, usually `sqrt n`. -/
noncomputable def twoSLSFunctionWaldStatOrZero
    {r : ℕ} (rfun : (k → ℝ) → (Fin r → ℝ)) (θ0 : Fin r → ℝ)
    (Rhat : Matrix k (Fin r) ℝ) (Vhatβ : Matrix k k ℝ)
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (root : ℝ) : ℝ :=
  restrictionWaldStatOrZero
    (root • (rfun (twoSLSBetaStar Z X Y) - θ0))
    (twoSLSFunctionVHat Vhatβ Rhat)

section Covariance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq k] in
/-- Hansen Theorem 12.5 covariance half: if `V̂β →p Vβ` and the estimated
derivative matrix `R̂ →p R`, then `R̂' V̂β R̂ →p R' Vβ R`. -/
theorem twoSLSFunctionVHat_tendstoInMeasure
    {Vhatβ : ℕ → Ω → Matrix k k ℝ} {Rhat : ℕ → Ω → Matrix k q ℝ}
    {Vβ : Matrix k k ℝ} {R : Matrix k q ℝ}
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hV : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hR : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TendstoInMeasure μ
      (fun t ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω))
      atTop (fun _ => twoSLSFunctionVariance Vβ R) := by
  have hRT_meas : ∀ t : ℕ, AEStronglyMeasurable (fun ω => (Rhat t ω)ᵀ) μ :=
    fun t => (continuous_id.matrix_transpose).comp_aestronglyMeasurable (hR_meas t)
  have hRT : TendstoInMeasure μ
      (fun t ω => (Rhat t ω)ᵀ) atTop (fun _ => Rᵀ) :=
    tendstoInMeasure_continuous_comp hR_meas hR continuous_id.matrix_transpose
  simpa [twoSLSFunctionVHat, twoSLSFunctionVariance, Matrix.transpose_transpose] using
    randomLinearMapCovariance_tendstoInMeasure
      (μ := μ) (Rhat := fun t ω => (Rhat t ω)ᵀ) (R := Rᵀ)
      (Vhat := Vhatβ) (V := Vβ) hRT_meas hV_meas hRT hV

end Covariance

section SmoothRemainder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Taylor remainder for Hansen's smooth function notation:
`r(b) - r(β) - Rᵀ(b-β)`. -/
noncomputable def twoSLSFunctionTaylorRemainder
    (rfun : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (R : Matrix k q ℝ) :
    (k → ℝ) → (q → ℝ) :=
  fun b => rfun b - rfun β - Rᵀ *ᵥ (b - β)

omit [DecidableEq k] [IsProbabilityMeasure μ] in
/-- Assumption 7.3 plus consistency and bounded scaled coefficient error make
the smooth-function Taylor remainder negligible after the same normalization. -/
theorem twoSLSFunction_scaled_taylor_remainder_tendstoInMeasure_of_consistency_bounded
    {rfun : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SmoothFunctionAssumption73 rfun β R)
    (root : ℕ → ℝ) (βhat : ℕ → Ω → k → ℝ)
    (hβ : TendstoInMeasure μ βhat atTop (fun _ => β))
    (hTβ : BoundedInProbabilityNorm μ
      (fun n ω => root n • (βhat n ω - β))) :
    TendstoInMeasure μ
      (fun n ω => root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hβ ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' ENNReal.ofNat_ne_top
  obtain ⟨M, hMpos, hMev⟩ := hTβ (δ / 2) hδ2
  let η : ℝ := ε / M
  have hηpos : 0 < η := div_pos hε hMpos
  have hnear :
      ∀ᶠ b in 𝓝 β,
        ‖twoSLSFunctionTaylorRemainder rfun β R b‖ ≤ η * ‖b - β‖ := by
    simpa [twoSLSFunctionTaylorRemainder] using
      (SmoothFunctionAssumption73.taylorRemainder_isLittleO h73).def hηpos
  rcases Metric.mem_nhds_iff.1 hnear with ⟨ρ, hρpos, hρsub⟩
  have hβev := (hβ ρ hρpos).eventually_lt_const hδ2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hMev.and hβev)
  refine ⟨N, fun n hnN => ?_⟩
  have hnM : μ {ω | M ≤ ‖root n • (βhat n ω - β)‖} ≤ δ / 2 := (hN n hnN).1
  have hnβ : μ {ω | ρ ≤ dist (βhat n ω) β} < δ / 2 := (hN n hnN).2
  have hnβ_le : μ {ω | ρ ≤ dist (βhat n ω) β} ≤ δ / 2 := le_of_lt hnβ
  have hcover :
      {ω | ε ≤ dist
        (root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)) 0} ⊆
        {ω | M ≤ ‖root n • (βhat n ω - β)‖} ∪
          {ω | ρ ≤ dist (βhat n ω) β} := by
    intro ω hω
    by_cases hTbig : M ≤ ‖root n • (βhat n ω - β)‖
    · exact Or.inl hTbig
    right
    by_contra hβbig
    have hTsmall : ‖root n • (βhat n ω - β)‖ < M := not_le.mp hTbig
    have hβsmall : dist (βhat n ω) β < ρ := not_le.mp hβbig
    have hbmem : βhat n ω ∈ Metric.ball β ρ := by
      simpa [Metric.mem_ball, dist_comm] using hβsmall
    have hrem_bound :
        ‖twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)‖ ≤
          η * ‖βhat n ω - β‖ :=
      hρsub hbmem
    have hscaled_bound :
        ‖root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)‖ ≤
          η * ‖root n • (βhat n ω - β)‖ := by
      calc
        ‖root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)‖
            = ‖root n‖ * ‖twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)‖ :=
              norm_smul _ _
        _ ≤ ‖root n‖ * (η * ‖βhat n ω - β‖) :=
              mul_le_mul_of_nonneg_left hrem_bound (norm_nonneg _)
        _ = η * (‖root n‖ * ‖βhat n ω - β‖) := by ring
        _ = η * ‖root n • (βhat n ω - β)‖ := by rw [norm_smul]
    have hscaled_lt :
        ‖root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)‖ < ε := by
      calc
        ‖root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)‖
            ≤ η * ‖root n • (βhat n ω - β)‖ := hscaled_bound
        _ < η * M := mul_lt_mul_of_pos_left hTsmall hηpos
        _ = ε := div_mul_cancel₀ ε hMpos.ne'
    have hdist_lt :
        dist (root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)) 0 < ε := by
      simpa [dist_eq_norm] using hscaled_lt
    exact (not_le_of_gt hdist_lt) hω
  calc
    μ {ω | ε ≤ dist
        (root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω)) 0}
        ≤ μ ({ω | M ≤ ‖root n • (βhat n ω - β)‖} ∪
          {ω | ρ ≤ dist (βhat n ω) β}) := measure_mono hcover
    _ ≤ μ {ω | M ≤ ‖root n • (βhat n ω - β)‖} +
          μ {ω | ρ ≤ dist (βhat n ω) β} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hnM hnβ_le
    _ = δ := ENNReal.add_halves δ

omit [DecidableEq k] [IsProbabilityMeasure μ] in
/-- Convert a negligible smooth-function Taylor remainder into the centered
linearization used by Theorem 12.5. -/
theorem twoSLSFunction_linearization_of_scaled_taylor_remainder
    {rfun : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (root : ℕ → ℝ) (βhat : ℕ → Ω → k → ℝ)
    (hrem : TendstoInMeasure μ
      (fun n ω => root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      ((fun n ω => root n • (rfun (βhat n ω) - rfun β)) -
        fun n ω => Rᵀ *ᵥ (root n • (βhat n ω - β)))
      atTop (fun _ => 0) := by
  have heq :
      ((fun n ω => root n • (rfun (βhat n ω) - rfun β)) -
          fun n ω => Rᵀ *ᵥ (root n • (βhat n ω - β))) =
        fun n ω => root n • twoSLSFunctionTaylorRemainder rfun β R (βhat n ω) := by
    funext n ω
    ext j
    simp [twoSLSFunctionTaylorRemainder, sub_eq_add_neg, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_neg, smul_neg, smul_eq_mul]
    ring_nf
  simpa [heq] using hrem

omit [DecidableEq k] [IsProbabilityMeasure μ] in
/-- Hansen Assumption 7.3 bridge for Theorems 12.5--12.6.

The smooth-function package, coefficient consistency, and bounded scaled
coefficient error imply the exact function-level linearization used by the
2SLS delta-method and Wald wrappers. -/
theorem twoSLSFunction_linearization_of_assumption73_consistency_bounded
    {rfun : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SmoothFunctionAssumption73 rfun β R)
    (root : ℕ → ℝ) (βhat : ℕ → Ω → k → ℝ)
    (hβ : TendstoInMeasure μ βhat atTop (fun _ => β))
    (hTβ : BoundedInProbabilityNorm μ
      (fun n ω => root n • (βhat n ω - β))) :
    TendstoInMeasure μ
      ((fun n ω => root n • (rfun (βhat n ω) - rfun β)) -
        fun n ω => Rᵀ *ᵥ (root n • (βhat n ω - β)))
      atTop (fun _ => 0) :=
  twoSLSFunction_linearization_of_scaled_taylor_remainder
    (μ := μ) (rfun := rfun) (β := β) (R := R)
    root βhat
    (twoSLSFunction_scaled_taylor_remainder_tendstoInMeasure_of_consistency_bounded
      (μ := μ) h73 root βhat hβ hTβ)

/-- Convert the raw `q → ℝ` function linearization into the Euclidean-space
linearization used by the Gaussian Delta-method wrappers. -/
theorem twoSLSFunction_euclidean_linearization_of_raw
    {rfun : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (root : ℕ → ℝ) (βhat : ℕ → Ω → k → ℝ)
    (hraw_meas : ∀ n : ℕ, AEStronglyMeasurable
      (((fun n ω => root n • (rfun (βhat n ω) - rfun β)) -
        fun n ω => Rᵀ *ᵥ (root n • (βhat n ω - β))) n) μ)
    (hraw : TendstoInMeasure μ
      ((fun n ω => root n • (rfun (βhat n ω) - rfun β)) -
        fun n ω => Rᵀ *ᵥ (root n • (βhat n ω - β)))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      ((fun n ω =>
        (WithLp.toLp 2 (root n • (rfun (βhat n ω) - rfun β)) :
          EuclideanSpace ℝ q)) -
        fun n ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2 (root n • (βhat n ω - β))))
      atTop (fun _ => 0) := by
  have hto : TendstoInMeasure μ
      (fun n ω =>
        (WithLp.toLp 2
          ((((fun n ω => root n • (rfun (βhat n ω) - rfun β)) -
            fun n ω => Rᵀ *ᵥ (root n • (βhat n ω - β))) n ω)) :
          EuclideanSpace ℝ q))
      atTop (fun _ => 0) :=
    tendstoInMeasure_continuous_comp hraw_meas hraw
      (PiLp.continuous_toLp 2 (fun _ : q => ℝ))
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hto
  exact ae_of_all μ (fun ω => by
    ext j
    simp [matrixContinuousLinearMap_apply, sub_eq_add_neg, Matrix.mulVec_add,
      Matrix.mulVec_neg, Matrix.mulVec_smul, smul_eq_mul])

end SmoothRemainder

section Consistency

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

set_option linter.unusedFintypeInType false in
omit [IsProbabilityMeasure μ] in
/-- Finite-sample measurability of Hansen's smooth-function 2SLS estimator from
row measurability and Borel measurability of `r`. -/
theorem twoSLSFunctionEstimator_aestronglyMeasurable_of_rows
    {rfun : (k → ℝ) → (q → ℝ)}
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hrfun : Measurable rfun)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ := by
  have hβ :
      AEStronglyMeasurable
        (fun ω =>
          twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω)) μ :=
    twoSLSBetaStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  rw [aestronglyMeasurable_iff_aemeasurable]
  exact hrfun.comp_aemeasurable hβ.aemeasurable

set_option linter.unusedFintypeInType false in
omit [IsProbabilityMeasure μ] in
/-- Finite-sample measurability of the textbook-facing smooth-function 2SLS
estimator from row measurability and Borel measurability of `r`. -/
theorem twoSLSFunctionEstimatorOrZero_aestronglyMeasurable_of_rows
    {rfun : (k → ℝ) → (q → ℝ)}
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hrfun : Measurable rfun)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ := by
  simpa [twoSLSFunctionEstimatorOrZero_eq_star] using
    twoSLSFunctionEstimator_aestronglyMeasurable_of_rows
      (μ := μ) (rfun := rfun) (Z := Z) (X := X) (Y := Y) hrfun hZ hX hY

/-- Hansen Theorem 12.4 interface: consistency of smooth functions of 2SLS.

Once `β̂₂ₛₗₛ →p β`, the continuous-mapping theorem gives
`r(β̂₂ₛₗₛ) →p r(β)`. Assumption 7.3 supplies the required continuity at `β`. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hβ : TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β))
    (hr : ContinuousAt rfun β) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  smoothFunction_consistency hβ_meas hr_meas hβ hr

/-- Hansen Theorem 12.4, textbook-facing OrZero endpoint from the Chapter 12.1
2SLS consistency theorem and Hansen Assumption 7.3's continuity consequence. -/
theorem twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_linearization
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {β : k → ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX)
    (hlinearization : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) - β) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            sampleCrossMoment (fun i : Fin t => Z i.val ω)
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0))
    (hr : ContinuousAt rfun β) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  smoothFunction_consistency hβ_meas hr_meas
    (twoSLSBetaOrZero_tendstoInMeasure_beta_of_linearization
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hlinearization)
    hr

/-- Hansen Theorem 12.4 Star endpoint from the structural 2SLS consistency
theorem and Hansen Assumption 7.3's continuity consequence. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure_of_model_nonsingular
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {β : k → ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hr : ContinuousAt rfun β) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  twoSLSFunctionEstimator_tendstoInMeasure hβ_meas hr_meas
    (twoSLSBetaStar_tendstoInMeasure_beta_of_model_nonsingular
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hunit)
    hr

/-- Hansen Theorem 12.4 textbook-facing OrZero endpoint from the structural
2SLS consistency theorem and Hansen Assumption 7.3's continuity consequence. -/
theorem twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_model_nonsingular
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {β : k → ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hr : ContinuousAt rfun β) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  smoothFunction_consistency hβ_meas hr_meas
    (twoSLSBetaOrZero_tendstoInMeasure_beta_of_model_nonsingular
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hunit)
    hr

/-- Hansen Theorem 12.4 Star endpoint from sample-moment convergence and the
structural equation, deriving high-probability nonsingularity internally. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure_of_sample_moments_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {β : k → ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hr : ContinuousAt rfun β) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  twoSLSFunctionEstimator_tendstoInMeasure hβ_meas hr_meas
    (twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)
    hr

/-- Hansen Theorem 12.4 textbook-facing OrZero endpoint from sample-moment
convergence and the structural equation. -/
theorem twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_sample_moments_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {β : k → ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hr : ContinuousAt rfun β) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  smoothFunction_consistency hβ_meas hr_meas
    (twoSLSBetaOrZero_tendstoInMeasure_beta_of_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)
    hr

/-- Hansen Theorem 12.4 Star endpoint from the Hansen-facing Assumption 12.1
condition package and Assumption 7.3 smoothness. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure_of_assumption12_1_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1Conditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  twoSLSFunctionEstimator_tendstoInMeasure hβ_meas hr_meas
    (twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)
    h73.continuousAt

/-- Hansen Theorem 12.4 textbook-facing OrZero endpoint from the Hansen-facing
Assumption 12.1 condition package and Assumption 7.3 smoothness. -/
theorem twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_assumption12_1_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1Conditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  smoothFunction_consistency hβ_meas hr_meas
    (twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)
    h73.continuousAt

/-- Hansen Theorem 12.4 Star endpoint from the primitive Assumption 12.1 Gram
package and Assumption 7.3 smoothness.

This wrapper avoids the older proof-facing Assumption 12.1 package that carried
an unnecessary nonsingularity condition on the full combined `[Z,X]` Gram. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure_of_assumption12_1_gram_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1GramConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  twoSLSFunctionEstimator_tendstoInMeasure hβ_meas hr_meas
    (twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_gram_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)
    h73.continuousAt

/-- Hansen Theorem 12.4 textbook-facing OrZero endpoint from the primitive
Assumption 12.1 Gram package and Assumption 7.3 smoothness. -/
theorem twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_assumption12_1_gram_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1GramConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  smoothFunction_consistency hβ_meas hr_meas
    (twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_gram_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)
    h73.continuousAt

/-- Hansen Theorem 12.4 Star endpoint from the iid finite-second Assumption
12.1 package and Assumption 7.3 smoothness. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure_of_assumption12_1_iid_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1IidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  twoSLSFunctionEstimator_tendstoInMeasure hβ_meas hr_meas
    (twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)
    h73.continuousAt

/-- Hansen Theorem 12.4 textbook-facing OrZero endpoint from the iid
finite-second Assumption 12.1 package and Assumption 7.3 smoothness. -/
theorem twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_assumption12_1_iid_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1IidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  smoothFunction_consistency hβ_meas hr_meas
    (twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)
    h73.continuousAt

/-- Hansen Theorem 12.4 Star endpoint from the single-row iid Assumption 12.1
package and Assumption 7.3 smoothness. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure_of_assumption12_1_joint_iid_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1JointIidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  twoSLSFunctionEstimator_tendstoInMeasure_of_assumption12_1_iid_73_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    hβ_meas hr_meas h.toIidConditions hmodel h73

/-- Hansen Theorem 12.4 textbook-facing OrZero endpoint from the single-row iid
Assumption 12.1 package and Assumption 7.3 smoothness. -/
theorem twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_assumption12_1_joint_iid_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1JointIidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) :=
  twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_assumption12_1_iid_73_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    hβ_meas hr_meas h.toIidConditions hmodel h73

/-- Hansen Theorem 12.4 Star endpoint from the single-row iid Assumption 12.1
package and Assumption 7.3 smoothness, with the exact transformed-estimator
measurability side condition exposed directly.

This is the theorem-facing route when one does not want to assume global
Borel-measurability of `rfun`. Assumption 7.3 supplies the local continuity used
by the continuous-mapping theorem; finite-sample measurability of
`rfun (βhat)` is the only remaining technical measurability input. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure_of_joint_iid_73_aestronglyMeasurable
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1JointIidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    fun _ =>
      twoSLSBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  exact
    twoSLSFunctionEstimator_tendstoInMeasure_of_assumption12_1_joint_iid_73_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hβ_meas hr_meas h hmodel h73

/-- Hansen Theorem 12.4 textbook-facing OrZero endpoint from the single-row iid
Assumption 12.1 package and Assumption 7.3 smoothness, with transformed
estimator measurability supplied directly instead of global measurability of
`rfun`. -/
theorem
    twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_joint_iid_73_aestronglyMeasurable
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1JointIidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    fun _ =>
      twoSLSBetaOrZero_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  exact
    twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_assumption12_1_joint_iid_73_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hβ_meas hr_meas h hmodel h73

/-- Hansen Theorem 12.4 Star endpoint from the literal observed-row finite
second-moment Assumption 12.1 package and Assumption 7.3 smoothness. -/
theorem
    twoSLSFunctionEstimator_tendstoInMeasure_of_textbook12_1_joint_iid_second_73
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k q ℝ}
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1JointIidTextbookSecondConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β0) :=
  twoSLSFunctionEstimator_tendstoInMeasure_of_joint_iid_73_aestronglyMeasurable
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    hr_meas h.toJointIidConditions h.model h73

/-- Hansen Theorem 12.4 OrZero endpoint from the literal observed-row finite
second-moment Assumption 12.1 package and Assumption 7.3 smoothness. -/
theorem
    twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_textbook12_1_joint_iid_second_73
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k q ℝ}
    (hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (h : TwoSLSAssumption12_1JointIidTextbookSecondConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β0) :=
  twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_joint_iid_73_aestronglyMeasurable
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    hr_meas h.toJointIidConditions h.model h73

/-- Hansen Theorem 12.4 Star endpoint from the single-row iid Assumption 12.1
package, deriving the technical measurability hypotheses from row
measurability and Borel measurability of the smooth map. -/
theorem twoSLSFunctionEstimator_tendstoInMeasure_of_joint_iid_73_measurable
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_1JointIidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    fun _ =>
      twoSLSBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  have hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    fun _ =>
      twoSLSFunctionEstimator_aestronglyMeasurable_of_rows
        (μ := μ) (rfun := rfun) (Z := Z) (X := X) (Y := Y)
        hrfun h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  exact
    twoSLSFunctionEstimator_tendstoInMeasure_of_assumption12_1_joint_iid_73_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hβ_meas hr_meas h hmodel h73

/-- Hansen Theorem 12.4 textbook-facing endpoint from the single-row iid
Assumption 12.1 package, deriving the technical measurability hypotheses from
row measurability and Borel measurability of the smooth map. -/
theorem twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_joint_iid_73_measurable
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_1JointIidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β) := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    fun _ =>
      twoSLSBetaOrZero_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  have hr_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    fun _ =>
      twoSLSFunctionEstimatorOrZero_aestronglyMeasurable_of_rows
        (μ := μ) (rfun := rfun) (Z := Z) (X := X) (Y := Y)
        hrfun h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  exact
    twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_assumption12_1_joint_iid_73_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hβ_meas hr_meas h hmodel h73

/-- Hansen Theorem 12.4 Star endpoint from the literal observed-row finite
second-moment Assumption 12.1 package, deriving finite-sample transformed
estimator measurability from Borel measurability of `rfun`. -/
theorem
    twoSLSFunctionEstimator_tendstoInMeasure_of_textbook12_1_joint_iid_second_73_borel
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_1JointIidTextbookSecondConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimator rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β0) :=
  twoSLSFunctionEstimator_tendstoInMeasure_of_joint_iid_73_measurable
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    hrfun h.toJointIidConditions h.model h73

/-- Hansen Theorem 12.4 OrZero endpoint from the literal observed-row finite
second-moment Assumption 12.1 package, deriving finite-sample transformed
estimator measurability from Borel measurability of `rfun`. -/
theorem
    twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_textbook12_1_joint_iid_second_73_borel
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_1JointIidTextbookSecondConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSFunctionEstimatorOrZero rfun
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => rfun β0) :=
  twoSLSFunctionEstimatorOrZero_tendstoInMeasure_of_joint_iid_73_measurable
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    hrfun h.toJointIidConditions h.model h73

end Consistency

section Normality

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ν : Measure Ω'} [IsProbabilityMeasure ν]

/-- Hansen Theorem 12.5 distribution half: Delta-method normality for a smooth
function of the 2SLS coefficient estimator.

The derivative matrix follows Hansen's orientation, `R = ∂r(β)'/∂β`, so the
Gaussian covariance is `R' Vβ R`. -/
theorem twoSLSFunctionEstimator_tendstoInDistribution_gaussian
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k q ℝ}
    (hVβ : Vβ.PosSemidef)
    (hβ : TendstoInDistribution
      (fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSBetaStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - β)) :
          EuclideanSpace ℝ k))
      atTop (fun z : EuclideanSpace ℝ k => z) (fun _ => μ)
      (multivariateGaussian 0 Vβ))
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimator rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimator rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimator rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q))
      atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
      (multivariateGaussian 0 (twoSLSFunctionVariance Vβ R)) := by
  have h := smoothFunction_asymptoticNormality_gaussian
    (k := k) (q := q) (S := Vβ) (R := Rᵀ)
    hVβ hβ hrem hθ_meas
  simpa [twoSLSFunctionVariance, Matrix.transpose_transpose] using h

/-- **Hansen Theorem 12.5.**

Textbook-facing nonlinear 2SLS theorem: the smooth transformed estimator has
the Delta-method Gaussian limit, and the plug-in covariance transform is
consistent. The coefficient CLT is supplied by the Chapter 12.2 condition
package, while the function-level Taylor remainder is the Assumption 7.3
linearization input. -/
theorem twoSLSFunction_theorem12_5
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k q ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k q ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hlinearizationβ : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            (Real.sqrt (t : ℝ) •
              sampleCrossMoment (fun i : Fin t => Z i.val ω)
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0))
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0 (twoSLSFunctionVariance Vβ R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω))
        atTop (fun _ => twoSLSFunctionVariance Vβ R) := by
  have hβstar_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ := by
    intro t
    simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hβ_meas t
  have hβraw :=
    twoSLSBetaStar_tendstoInDistribution_of_linearization
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hAN β hlinearizationβ hβstar_meas
  have hβeuclid :
      TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSBetaStar
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - β)) :
            EuclideanSpace ℝ k))
        atTop (fun z : EuclideanSpace ℝ k => z) (fun _ => μ)
        (multivariateGaussian 0 Vβ) := by
    have hmap := hβraw.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [Function.comp_def] using hmap
  have hrem_star : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimator rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0) := by
    simpa [twoSLSFunctionEstimatorOrZero_eq_star] using hrem
  have hθ_meas_star : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimator rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) μ := by
    intro t
    simpa [twoSLSFunctionEstimatorOrZero_eq_star] using hθ_meas t
  have hθ_star :=
    twoSLSFunctionEstimator_tendstoInDistribution_gaussian
      (μ := μ) (q := q) (rfun := rfun) (Z := Z) (X := X) (Y := Y)
      (β := β) (Vβ := Vβ) (R := R)
      hVβ hβeuclid hrem_star hθ_meas_star
  have hθ :
      TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0 (twoSLSFunctionVariance Vβ R)) := by
    simpa [twoSLSFunctionEstimatorOrZero_eq_star] using hθ_star
  exact ⟨hθ,
    twoSLSFunctionVHat_tendstoInMeasure
      (μ := μ) (Vhatβ := Vhatβ) (Rhat := Rhat) (Vβ := Vβ) (R := R)
      hV_meas hR_meas hVhatβ hRhat⟩

/-- Assumption 7.3 remainder bridge for Hansen Theorem 12.5 under the
single-row iid Assumption 12.2 package.

This discharges the function-level Delta-method remainder from coefficient
consistency, boundedness of the root-scaled 2SLS estimator supplied by Theorem
12.2, and the smoothness package for `r`. -/
theorem twoSLSFunction_remainder_tendstoInMeasure_of_assumption12_2_joint_iid_73_model
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k q ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ q)) μ) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ q)) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β0))))
      atTop (fun _ => 0) := by
  let βhat : ℕ → Ω → k → ℝ := fun t ω =>
    twoSLSBetaStar
      (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
      (fun i : Fin t => Y i.val ω)
  have hβdist :=
    twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β0 hmodel
  have hβ : TendstoInMeasure μ βhat atTop (fun _ => β0) := by
    simpa [βhat] using
      twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_joint_iid_model
        (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
        h.toTwoSLSAssumption12_1JointIidConditions β0 hmodel
  have hTβ : BoundedInProbabilityNorm μ
      (fun t ω => Real.sqrt (t : ℝ) • (βhat t ω - β0)) := by
    simpa [βhat] using
      (BoundedInProbabilityNorm.of_tendstoInDistribution
        (μ := μ) (X := fun t ω =>
          Real.sqrt (t : ℝ) •
            (twoSLSBetaStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - β0))
        hβdist)
  have hraw_meas : ∀ t : ℕ, AEStronglyMeasurable
      (((fun (m : ℕ) ω => Real.sqrt (m : ℝ) • (rfun (βhat m ω) - rfun β0)) -
        fun (m : ℕ) ω => Rᵀ *ᵥ (Real.sqrt (m : ℝ) • (βhat m ω - β0))) t) μ := by
    intro t
    have hθ_star : AEMeasurable
        (fun ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimator rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q)) μ := by
      simpa [twoSLSFunctionEstimatorOrZero_eq_star] using hθ_meas t
    have hθ_raw_aemeas : AEMeasurable
        (fun ω =>
          Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimator rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) μ := by
      have hcomp := (PiLp.continuous_ofLp 2 (fun _ : q => ℝ)).measurable.comp_aemeasurable
        hθ_star
      simpa [Function.comp_def] using hcomp
    have hθ_raw : AEStronglyMeasurable
        (fun ω => Real.sqrt (t : ℝ) • (rfun (βhat t ω) - rfun β0)) μ := by
      simpa [βhat, twoSLSFunctionEstimator] using hθ_raw_aemeas.aestronglyMeasurable
    have hβ_scaled : AEStronglyMeasurable
        (fun ω => Real.sqrt (t : ℝ) • (βhat t ω - β0)) μ := by
      have hβ_aemeas := hβdist.forall_aemeasurable t
      simpa [βhat] using hβ_aemeas.aestronglyMeasurable
    have hlin : AEStronglyMeasurable
        (fun ω => Rᵀ *ᵥ (Real.sqrt (t : ℝ) • (βhat t ω - β0))) μ :=
      (Continuous.matrix_mulVec continuous_const continuous_id).comp_aestronglyMeasurable
        hβ_scaled
    exact hθ_raw.sub hlin
  have hraw : TendstoInMeasure μ
      ((fun (m : ℕ) ω => Real.sqrt (m : ℝ) • (rfun (βhat m ω) - rfun β0)) -
        fun (m : ℕ) ω => Rᵀ *ᵥ (Real.sqrt (m : ℝ) • (βhat m ω - β0)))
      atTop (fun _ => 0) :=
    twoSLSFunction_linearization_of_assumption73_consistency_bounded
      (μ := μ) (rfun := rfun) (β := β0) (R := R)
      h73 (fun t => Real.sqrt (t : ℝ)) βhat hβ hTβ
  simpa [βhat, twoSLSFunctionEstimatorOrZero_eq_star] using
    twoSLSFunction_euclidean_linearization_of_raw
      (μ := μ) (rfun := rfun) (β := β0) (R := R)
      (fun t => Real.sqrt (t : ℝ)) βhat hraw_meas hraw

/-- Sharp remaining function-estimator surface for Hansen Theorems 12.5 and
12.6 under joint-iid Assumption 12.2 plus Assumption 7.3.

Assumption 12.2 supplies the coefficient CLT, coefficient consistency,
population rank facts, and the ideal covariance limits. `SmoothFunctionAssumption73`
supplies the local Taylor remainder once the transformed statistic is
measurable. The fields here isolate what those assumptions do not currently
imply in this file: the feasible covariance residual-substitution WLLN surface,
measurability of the transformed statistic, finite-sample measurability of the
feasible covariance estimator, and measurability/convergence of the derivative
estimator `Rhat`. -/
structure TwoSLSFunctionAssumption12_2JointIid73Conditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e Y : ℕ → Ω → ℝ)
    (rfun : (k → ℝ) → (q → ℝ)) (β0 : k → ℝ)
    (R : Matrix k q ℝ) (Rhat : ℕ → Ω → Matrix k q ℝ) : Prop where
  /-- Scalar WLLN package for the residual-substitution weights in Hansen
  Theorem 12.3's feasible 2SLS covariance estimator. -/
  covariance_weights : TwoSLSCovarianceWeightWLLNConditions μ Z X e
  /-- A.e. measurability of the normalized transformed estimator. This is kept
  separate because local differentiability at `β₀` does not by itself give
  global measurability of `ω ↦ r(βhat ω)`. -/
  theta_aemeasurable : ∀ t : ℕ, AEMeasurable
    (fun ω =>
      (WithLp.toLp 2
        (Real.sqrt (t : ℝ) •
          (twoSLSFunctionEstimatorOrZero rfun
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - rfun β0)) :
        EuclideanSpace ℝ q)) μ
  /-- A.e. strong measurability of the feasible robust 2SLS covariance
  estimator. `TendstoInMeasure` in this development is a convergence predicate,
  so this finite-sample measurability is not recovered from the covariance
  consistency field alone. -/
  covariance_aestronglyMeasurable : ∀ t : ℕ, AEStronglyMeasurable
    (fun ω =>
      twoSLSVHatStar
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω)) μ
  /-- A.e. strong measurability of the derivative estimator. -/
  derivative_aestronglyMeasurable : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ
  /-- Consistency of the derivative estimator for Hansen's derivative matrix. -/
  derivative_tendsto : TendstoInMeasure μ Rhat atTop (fun _ => R)

namespace TwoSLSFunctionAssumption12_2JointIid73Conditions

/-- Constructor from joint-iid Assumption 12.2 plus the exact mixed moment
summands used by Hansen Theorem 12.3's feasible covariance residual
substitution. Independence and identical distribution of those scalar weights
are derived from the joint iid row package; the other fields are precisely the
function/derivative-estimator obligations not implied by local Assumption 7.3. -/
theorem of_joint_iid_mixed_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {rfun : (k → ℝ) → (q → ℝ)} {β0 : k → ℝ}
    {R : Matrix k q ℝ} {Rhat : ℕ → Ω → Matrix k q ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ q)) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat where
  covariance_weights :=
    TwoSLSCovarianceWeightWLLNConditions.of_joint_iid
      (μ := μ) (Z := Z) (X := X) (e := e)
      h.joint_iIndep h.joint_identDistrib
      hOmegaCross hOmegaQuadratic hSigmaCross
  theta_aemeasurable := hθ_meas
  covariance_aestronglyMeasurable := hV_meas
  derivative_aestronglyMeasurable := hR_meas
  derivative_tendsto := hRhat

/-- Constructor for Hansen Theorems 12.5 and 12.6 that derives the finite-sample
function-statistic and robust-covariance measurability fields from joint row
measurability and measurability of `r`.

The remaining explicit fields are the mixed moments needed for Theorem 12.3's
residual-substitution WLLNs and the derivative-estimator convergence surface. -/
theorem of_joint_iid_mixed_moments_measurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {rfun : (k → ℝ) → (q → ℝ)} {β0 : k → ℝ}
    {R : Matrix k q ℝ} {Rhat : ℕ → Ω → Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat := by
  let h1 : TwoSLSAssumption12_1JointIidConditions μ Z X e :=
    h.toTwoSLSAssumption12_1JointIidConditions
  have hZ : ∀ i, AEStronglyMeasurable (Z i) μ :=
    h1.z_aestronglyMeasurable
  have hX : ∀ i, AEStronglyMeasurable (X i) μ :=
    h1.x_aestronglyMeasurable
  have he : ∀ i, AEStronglyMeasurable (e i) μ :=
    h1.e_aestronglyMeasurable
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β0 hX he hmodel
  have hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ q)) μ := by
    intro t
    have hθ0 : AEStronglyMeasurable
        (fun ω =>
          twoSLSFunctionEstimatorOrZero rfun
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) μ :=
      twoSLSFunctionEstimatorOrZero_aestronglyMeasurable_of_rows
        (μ := μ) (rfun := rfun) (Z := Z) (X := X) (Y := Y)
        hrfun hZ hX hY
    have hscaled : AEStronglyMeasurable
        (fun ω =>
          Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) μ :=
      (hθ0.sub aestronglyMeasurable_const).const_smul (Real.sqrt (t : ℝ))
    exact (PiLp.continuous_toLp 2 (fun _ : q => ℝ)).measurable.comp_aemeasurable
      hscaled.aemeasurable
  have hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    fun _ =>
      twoSLSVHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  exact of_joint_iid_mixed_moments
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (rfun := rfun) (β0 := β0) (R := R) (Rhat := Rhat)
    h hOmegaCross hOmegaQuadratic hSigmaCross
    hθ_meas hV_meas hR_meas hRhat

/-- Constructor for the direct-derivative specialization of Hansen Theorems
12.5--12.6.

When the plug-in derivative is the deterministic Hansen derivative matrix `R`
itself, joint-iid Assumption 12.2, measurability of `r`, and the mixed moment
summands used by Theorem 12.3 discharge all fields of the function condition
package. The derivative orientation and full-rank condition remain supplied by
`SmoothFunctionAssumption73` at the theorem endpoint. -/
theorem of_joint_iid_mixed_moments_measurable_const_derivative
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {rfun : (k → ℝ) → (q → ℝ)} {β0 : k → ℝ}
    {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ) :
    TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R (fun _ _ => R) := by
  refine of_joint_iid_mixed_moments_measurable
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (rfun := rfun) (β0 := β0) (R := R)
    (Rhat := fun (_ : ℕ) (_ : Ω) => R)
    hrfun h hmodel hOmegaCross hOmegaQuadratic hSigmaCross ?_ ?_
  · intro _
    exact aestronglyMeasurable_const
  · exact tendstoInMeasure_of_tendsto_ae
      (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => tendsto_const_nhds))

/-- Constructor for Hansen Theorems 12.5 and 12.6 from the packaged
Assumption 12.2 mixed-moment surface used by Theorem 12.3.

This is a notation bridge over
`of_joint_iid_mixed_moments_measurable`: the single package supplies the joint
iid fourth-moment assumptions and the exact mixed `e X Z Z`, `X X Z Z`, and
`e X` integrability fields needed for feasible covariance consistency. -/
theorem of_joint_iid_mixed_moment_conditions_measurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {rfun : (k → ℝ) → (q → ℝ)} {β0 : k → ℝ}
    {R : Matrix k q ℝ} {Rhat : ℕ → Ω → Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat :=
  of_joint_iid_mixed_moments_measurable
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (rfun := rfun) (β0 := β0) (R := R) (Rhat := Rhat)
    hrfun h.toTwoSLSAssumption12_2JointIidFourthConditions hmodel
    h.omega_cross_integrable h.omega_quadratic_integrable
    h.sigma_cross_integrable hR_meas hRhat

/-- Direct-derivative constructor from the packaged Assumption 12.2
mixed-moment surface used by Theorem 12.3. -/
theorem of_joint_iid_mixed_moment_conditions_measurable_const_derivative
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {rfun : (k → ℝ) → (q → ℝ)} {β0 : k → ℝ}
    {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω) :
    TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R (fun _ _ => R) :=
  of_joint_iid_mixed_moments_measurable_const_derivative
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (rfun := rfun) (β0 := β0) (R := R)
    hrfun h.toTwoSLSAssumption12_2JointIidFourthConditions hmodel
    h.omega_cross_integrable h.omega_quadratic_integrable
    h.sigma_cross_integrable

end TwoSLSFunctionAssumption12_2JointIid73Conditions

/-- Assumption 7.3 together with the plug-in derivative map used by Hansen
Theorems 12.5 and 12.6.

The matrix `R` is the population derivative `∂r(β₀)'/∂β`.  The map `Rfun`
represents the finite-sample derivative evaluated at an arbitrary coefficient
value, so Hansen's derivative estimator is `Rfun βhat`. The
`derivativeMap_hasFDerivAt` field prevents this package from being instantiated
with an arbitrary continuous matrix map that merely agrees with `R` at `β₀`. -/
structure SmoothFunctionPlugInDerivative73
    (rfun : (k → ℝ) → (q → ℝ)) (β0 : k → ℝ) (R : Matrix k q ℝ)
    (Rfun : (k → ℝ) → Matrix k q ℝ)
    extends SmoothFunctionAssumption73 rfun β0 R where
  /-- Locally around `β₀`, `Rfun b` is Hansen's transpose-oriented derivative
  matrix for `r` at `b`. -/
  derivativeMap_hasFDerivAt :
    ∀ᶠ b in 𝓝 β0, ∃ derivative : (k → ℝ) →L[ℝ] (q → ℝ),
      HasFDerivAt rfun derivative b ∧
        ∀ v : k → ℝ, derivative v = (Rfun b)ᵀ *ᵥ v
  /-- Global measurability needed for sample transformations of `r(βhat)`. -/
  function_measurable : Measurable rfun
  /-- The derivative map agrees with Hansen's population derivative at `β₀`. -/
  derivativeMap_at : Rfun β0 = R
  /-- Measurability needed for finite-sample plug-in derivative estimators. -/
  derivativeMap_measurable : Measurable Rfun
  /-- Continuity at `β₀`, the C¹ content needed for plug-in consistency. -/
  derivativeMap_continuousAt : ContinuousAt Rfun β0

namespace SmoothFunctionPlugInDerivative73

/-- The plug-in derivative estimator `Rfun(βhat₂SLS)` is strongly measurable
under row measurability and measurability of the derivative map. -/
theorem twoSLSDerivativePlugIn_aestronglyMeasurable_of_assumption12_1_joint_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {rfun : (k → ℝ) → (q → ℝ)} {β0 : k → ℝ} {R : Matrix k q ℝ}
    {Rfun : (k → ℝ) → Matrix k q ℝ}
    (h : TwoSLSAssumption12_1JointIidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun) :
    ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        Rfun
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))) μ := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β0
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  intro t
  have hβ : AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    twoSLSBetaOrZero_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y)
      h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  exact (h73.derivativeMap_measurable.comp_aemeasurable hβ.aemeasurable).aestronglyMeasurable

/-- Consistency of Hansen's plug-in derivative estimator
`Rhat = ∂r(βhat₂SLS)'/∂β`. -/
theorem twoSLSDerivativePlugIn_tendstoInMeasure_of_assumption12_1_joint_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {rfun : (k → ℝ) → (q → ℝ)} {β0 : k → ℝ} {R : Matrix k q ℝ}
    {Rfun : (k → ℝ) → Matrix k q ℝ}
    (h : TwoSLSAssumption12_1JointIidConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun) :
    TendstoInMeasure μ
      (fun t ω =>
        Rfun
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)))
      atTop (fun _ => R) := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β0
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hβ_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    fun t =>
      twoSLSBetaOrZero_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  have hR_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        Rfun
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))) μ :=
    twoSLSDerivativePlugIn_aestronglyMeasurable_of_assumption12_1_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h hmodel h73
  have hβ :
      TendstoInMeasure μ
        (fun t ω =>
          twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
        atTop (fun _ => β0) :=
    twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β0 hmodel
  have hplug :=
    smoothFunction_consistency
      (μ := μ)
      (θhat := fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      (θ := β0) (g := Rfun)
      hβ_meas hR_meas hβ h73.derivativeMap_continuousAt
  simpa [h73.derivativeMap_at] using hplug

end SmoothFunctionPlugInDerivative73

/-- **Hansen Theorem 12.5**, structural-model endpoint.

This wrapper reuses `twoSLSFunction_theorem12_5` and discharges its coefficient
linearization premise using the exact scaled 2SLS identity. The function-level
Taylor remainder and plug-in covariance consistency remain the Assumption
7.3/12.2 inputs. -/
theorem twoSLSFunction_theorem12_5_of_model_nonsingular
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k q ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k q ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0 (twoSLSFunctionVariance Vβ R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω))
        atTop (fun _ => twoSLSFunctionVariance Vβ R) :=
  twoSLSFunction_theorem12_5
    (μ := μ) (q := q) (rfun := rfun) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
    hAN hVβ
    (twoSLSBetaStar_sqrt_linearization_tendstoInMeasure_zero_of_model_nonsingular
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) β hmodel hunit)
    hβ_meas hrem hθ_meas hV_meas hR_meas hVhatβ hRhat

/-- **Hansen Theorem 12.5**, formula-facing 2SLS plug-in covariance endpoint.

This specializes `twoSLSFunction_theorem12_5_of_model_nonsingular` to the
actual robust 2SLS covariance estimator `twoSLSVHatStar`, with the coefficient
covariance limit fixed to Hansen's displayed 2SLS covariance formula. -/
theorem twoSLSFunction_theorem12_5_of_covariance_formula
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k q ℝ}
    {Rhat : ℕ → Ω → Matrix k q ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e
      (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
    (hVβ : (twoSLSAsymptoticVariance QXZ QZZ Omega QZX).PosSemidef)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ Omega QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rhat t ω))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) R) :=
  twoSLSFunction_theorem12_5_of_model_nonsingular
    (μ := μ) (q := q) (rfun := rfun) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (Vβ := twoSLSAsymptoticVariance QXZ QZZ Omega QZX) (R := R)
    (Vhatβ := fun t ω =>
      twoSLSVHatStar
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω))
    (Rhat := Rhat)
    hAN hVβ hmodel hunit hβ_meas hrem hθ_meas hV_meas hR_meas
    hcov.robust_tendsto hRhat

/-- **Hansen Theorem 12.5**, score-CLT/sample-moment constructor.

This is the formula-facing endpoint in the common case where Hansen's middle
matrix is the instrument-score covariance `Ω = Var(eZ)`. It reuses Chapter 7's
score CLT and the Chapter 12 sample-moment CMT to build the 2SLS normality
package, and derives positive-semidefiniteness of the displayed 2SLS sandwich
covariance from `Ω.PosSemidef`. -/
theorem twoSLSFunction_theorem12_5_of_scoreCLT_sample_moments
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k q ℝ}
    {Rhat : ℕ → Ω → Matrix k q ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ (scoreCovMat μ Z e) QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ q)) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rhat t ω))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX) R) :=
  twoSLSFunction_theorem12_5
    (μ := μ) (q := q) (rfun := rfun) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β)
    (Vβ := twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX)
    (R := R)
    (Vhatβ := fun t ω =>
      twoSLSVHatStar
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω))
    (Rhat := Rhat)
    (hMom.toFormulaAsymptoticNormalConditions hScore hQZZ_symm hQZX)
    (twoSLSAsymptoticVariance_posSemidef QXZ QZZ (scoreCovMat μ Z e) QZX
      (scoreCovMat_posSemidef (μ := μ) (X := Z) (e := e) hScore)
      hQZZ_symm hQZX)
    (twoSLSBetaStar_sqrt_linearization_tendstoInMeasure_zero_of_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) hMom β hmodel)
    hβ_meas hrem hθ_meas hV_meas hR_meas hcov.robust_tendsto hRhat

/-- **Hansen Theorem 12.5**, joint-iid Assumption 12.2 constructor.

This theorem composes the primitive single-row Assumption 12.2 package, the
Hansen Theorem 12.3 covariance constructor, and the generic nonlinear 2SLS
delta-method endpoint. The remaining explicit inputs are the Assumption-7.3
function linearization and derivative-estimator convergence surface. -/
theorem twoSLSFunction_theorem12_5_of_assumption12_2_joint_iid_moments
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k q ℝ}
    {Rhat : ℕ → Ω → Matrix k q ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ q)) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β0))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ q)) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rhat t ω))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) := by
  let hIid := h.toIidFourthConditions
  let hGram := hIid.toGramConditions
  let hMom := hGram.toTwoSLSAssumption12_1GramConditions.toSampleMomentConvergenceConditions
  have hQZZ_symm :
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ =
        twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h.qzz_posDef.1.eq
  have hQZX :
      twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)) =
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ :=
    twoSLSCombinedQZX_eq_transpose_QXZ_of_popGram_wlln
      (μ := μ) (Z := Z) (X := X) hGram.toTwoSLSAssumption12_1GramConditions.combined_gram
  have hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0)) μ :=
    (twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β0 hmodel).forall_aemeasurable
  exact twoSLSFunction_theorem12_5_of_scoreCLT_sample_moments
    (μ := μ) (q := q) (rfun := rfun)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β0)
    (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
    (sigma2 := errorVariance μ e) (R := R) (Rhat := Rhat)
    (hMom := hMom) (hScore := hGram.score_clt)
    (hQZZ_symm := hQZZ_symm) (hQZX := hQZX)
    (hcov :=
      TwoSLSCovarianceFormulaConsistencyConditions.of_assumption12_2_joint_iid_moments
        (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
        h β0 hmodel hOmegaCross hOmegaQuadratic hSigmaCross)
    (hmodel := hmodel) (hβ_meas := hβ_meas) (hrem := hrem)
    (hθ_meas := hθ_meas) (hV_meas := hV_meas)
    (hR_meas := hR_meas) (hRhat := hRhat)

/-- **Hansen Theorem 12.5**, joint-iid Assumption 12.2 plus Assumption 7.3.

This is the Hansen-facing smooth-function endpoint: the function-level
linearization is derived from Assumption 7.3, coefficient consistency, and the
Theorem 12.2 coefficient CLT instead of being supplied as a separate premise.
The remaining feasible-covariance and derivative-estimator obligations are
collected in `TwoSLSFunctionAssumption12_2JointIid73Conditions`. -/
theorem twoSLSFunction_theorem12_5_of_assumption12_2_joint_iid_73_model
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k q ℝ}
    {Rhat : ℕ → Ω → Matrix k q ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rhat t ω))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) :=
by
  let hIid := h.toIidFourthConditions
  let hGram := hIid.toGramConditions
  let hMom := hGram.toTwoSLSAssumption12_1GramConditions.toSampleMomentConvergenceConditions
  have hQZZ_symm :
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ =
        twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h.qzz_posDef.1.eq
  have hQZX :
      twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)) =
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ :=
    twoSLSCombinedQZX_eq_transpose_QXZ_of_popGram_wlln
      (μ := μ) (Z := Z) (X := X) hGram.toTwoSLSAssumption12_1GramConditions.combined_gram
  have hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0)) μ :=
    (twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β0 hmodel).forall_aemeasurable
  let hcov : TwoSLSCovarianceFormulaConsistencyConditions μ Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) :=
    TwoSLSCovarianceFormulaConsistencyConditions.of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h.toIidFourthConditions β0 hmodel hc.covariance_weights
  exact twoSLSFunction_theorem12_5_of_scoreCLT_sample_moments
    (μ := μ) (q := q) (rfun := rfun)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β0)
    (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
    (sigma2 := errorVariance μ e) (R := R) (Rhat := Rhat)
    (hMom := hMom) (hScore := hGram.score_clt)
    (hQZZ_symm := hQZZ_symm) (hQZX := hQZX)
    (hcov := hcov) (hmodel := hmodel) (hβ_meas := hβ_meas)
    (hrem :=
      twoSLSFunction_remainder_tendstoInMeasure_of_assumption12_2_joint_iid_73_model
        (μ := μ) (rfun := rfun) (Z := Z) (X := X) (e := e) (Y := Y)
        (β0 := β0) (R := R) h hmodel h73 hc.theta_aemeasurable)
    (hθ_meas := hc.theta_aemeasurable)
    (hV_meas := hc.covariance_aestronglyMeasurable)
    (hR_meas := hc.derivative_aestronglyMeasurable)
    (hRhat := hc.derivative_tendsto)

/-- **Hansen Theorem 12.5**, primitive joint-iid Assumption 12.2 plus
Assumption 7.3.

This theorem-facing wrapper constructs
`TwoSLSFunctionAssumption12_2JointIid73Conditions` internally from the primitive
single-row iid Assumption 12.2 package, measurability of `r`, and the mixed
third/fourth moment integrability hypotheses used by Hansen Theorem 12.3's
feasible covariance constructor. The only remaining estimator-specific inputs
are measurability and consistency of the plug-in derivative `Rhat`. -/
theorem twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moments_measurable
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k q ℝ}
    {Rhat : ℕ → Ω → Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rhat t ω))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) := by
  let hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat :=
    TwoSLSFunctionAssumption12_2JointIid73Conditions.of_joint_iid_mixed_moments_measurable
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (rfun := rfun) (β0 := β0) (R := R) (Rhat := Rhat)
      hrfun h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR_meas hRhat
  exact
    twoSLSFunction_theorem12_5_of_assumption12_2_joint_iid_73_model
      (μ := μ) (q := q) (rfun := rfun)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (Rhat := Rhat)
      h β0 hmodel h73 hc

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.5**, primitive joint-iid Assumption 12.2 plus
Assumption 7.3, with the plug-in derivative fixed at Hansen's derivative
matrix `R`.

This is the direct-derivative specialization of
`twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moments_measurable`: the
finite-sample derivative sequence is the deterministic matrix `R`, so the
derivative-estimator measurability and convergence premises are discharged by
`TwoSLSFunctionAssumption12_2JointIid73Conditions.of_joint_iid_mixed_moments_measurable_const_derivative`.
-/
theorem twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moments_measurable_const_derivative
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          R)
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) := by
  let hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R (fun _ _ => R) :=
    TwoSLSFunctionAssumption12_2JointIid73Conditions.of_joint_iid_mixed_moments_measurable_const_derivative
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (rfun := rfun) (β0 := β0) (R := R)
      hrfun h hmodel hOmegaCross hOmegaQuadratic hSigmaCross
  exact
    twoSLSFunction_theorem12_5_of_assumption12_2_joint_iid_73_model
      (μ := μ) (q := q) (rfun := rfun)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (Rhat := fun _ _ => R)
      h β0 hmodel h73 hc

/-- **Hansen Theorem 12.5**, packaged Assumption 12.2 mixed-moment route.

This is the theorem-facing version of
`twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moments_measurable` when the
caller already has the canonical Theorem 12.3 package
`TwoSLSAssumption12_2JointIidMixedMomentConditions`. -/
theorem twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moment_conditions_measurable
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k q ℝ}
    {Rhat : ℕ → Ω → Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R)) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rhat t ω))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) :=
  twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moments_measurable
    (μ := μ) (q := q) (rfun := rfun)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rhat := Rhat)
    hrfun h.toTwoSLSAssumption12_2JointIidFourthConditions β0 hmodel h73
    h.omega_cross_integrable h.omega_quadratic_integrable
    h.sigma_cross_integrable hR_meas hRhat

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.5**, packaged Assumption 12.2 mixed-moment route with
Hansen's plug-in derivative estimator
`Rhat = ∂r(βhat₂SLS)'/∂β`.

Compared with
`twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moment_conditions_measurable`,
this wrapper derives the derivative-estimator measurability and consistency
from the derivative map in `SmoothFunctionPlugInDerivative73`. -/
theorem
    twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moment_conditions_measurable_derivativePlugIn
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k q ℝ} {Rfun : (k → ℝ) → Matrix k q ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rfun
            (twoSLSBetaOrZero
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) := by
  let Rhat : ℕ → Ω → Matrix k q ℝ := fun t ω =>
    Rfun
      (twoSLSBetaOrZero
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω))
  let h12_2 : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e :=
    h.toTwoSLSAssumption12_2JointIidFourthConditions
  let h12_1 : TwoSLSAssumption12_1JointIidConditions μ Z X e :=
    h12_2.toTwoSLSAssumption12_1JointIidConditions
  have hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ :=
    SmoothFunctionPlugInDerivative73.twoSLSDerivativePlugIn_aestronglyMeasurable_of_assumption12_1_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h12_1 hmodel h73
  have hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R) :=
    SmoothFunctionPlugInDerivative73.twoSLSDerivativePlugIn_tendstoInMeasure_of_assumption12_1_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h12_1 hmodel h73
  simpa [Rhat] using
    twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moment_conditions_measurable
      (μ := μ) (q := q) (rfun := rfun)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (Rhat := Rhat)
      h73.function_measurable h β0 hmodel h73.toSmoothFunctionAssumption73 hR_meas hRhat

/-- **Hansen Theorem 12.5**, literal joint-iid Assumption 12.2 plus
Assumption 7.3 with Hansen's plug-in derivative estimator
`Rhat = ∂r(βhat₂SLS)'/∂β`.

This is the theorem-facing endpoint matching Hansen's finite-fourth-moment
Assumption 12.2 surface.  The mixed moments used by the feasible covariance
proof are derived from `E[Y₁⁴]`, `E‖X₁‖⁴`, and `E‖Z₁‖⁴`. -/
theorem twoSLSFunction_theorem12_5_of_textbook12_2_joint_iid_73_derivativePlugIn
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    {R : Matrix k q ℝ} {Rfun : (k → ℝ) → Matrix k q ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rfun
            (twoSLSBetaOrZero
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) :=
  twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moment_conditions_measurable_derivativePlugIn
    (μ := μ) (q := q) (rfun := rfun)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rfun := Rfun)
    h.toJointIidMixedMomentConditions β0 h.model h73

/-- **Hansen Theorem 12.5**, packaged Assumption 12.2 mixed-moment route with
Hansen's derivative estimator fixed at the deterministic matrix `R`. -/
theorem
    twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moment_conditions_measurable_const_derivative
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          R)
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) :=
  twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moments_measurable_const_derivative
    (μ := μ) (q := q) (rfun := rfun)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h.toTwoSLSAssumption12_2JointIidFourthConditions β0 hmodel h73
    h.omega_cross_integrable h.omega_quadratic_integrable
    h.sigma_cross_integrable

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.5**, literal joint-iid Assumption 12.2 plus
Assumption 7.3, with Hansen's derivative matrix fixed at `R`.

This compatibility endpoint keeps the deterministic-derivative theorem surface
at Hansen's finite-fourth-moment Assumption 12.2 layer. The preferred
theorem-facing endpoint is the plug-in derivative theorem, but linear
restrictions and other constant-derivative applications can use this wrapper
without manually unpacking the mixed covariance integrability consequences of
Assumption 12.2. -/
theorem twoSLSFunction_theorem12_5_of_textbook12_2_joint_iid_73_const_derivative
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          R)
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) :=
  twoSLSFunction_theorem12_5_of_joint_iid_73_mixed_moment_conditions_measurable_const_derivative
    (μ := μ) (q := q) (rfun := rfun)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h.toJointIidMixedMomentConditions β0 h.model h73

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.5**, literal observed-row iid Assumption 12.2 plus
Assumption 7.3 with Hansen's plug-in derivative estimator. -/
theorem twoSLSFunction_theorem12_5_of_textbook12_2_observed_iid_73_derivativePlugIn
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    {R : Matrix k q ℝ} {Rfun : (k → ℝ) → Matrix k q ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          (Rfun
            (twoSLSBetaOrZero
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))))
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) :=
  twoSLSFunction_theorem12_5_of_textbook12_2_joint_iid_73_derivativePlugIn
    (μ := μ) (q := q) (rfun := rfun)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rfun := Rfun)
    h.toResidualTextbookFourthConditions h73

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.5**, literal observed-row iid Assumption 12.2 plus
Assumption 7.3, with Hansen's derivative matrix fixed at `R`. -/
theorem twoSLSFunction_theorem12_5_of_textbook12_2_observed_iid_73_const_derivative
    [DecidableEq q]
    {rfun : (k → ℝ) → (q → ℝ)}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k q ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          (WithLp.toLp 2
            (Real.sqrt (t : ℝ) •
              (twoSLSFunctionEstimatorOrZero rfun
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω) - rfun β0)) :
            EuclideanSpace ℝ q))
        atTop (fun z : EuclideanSpace ℝ q => z) (fun _ => μ)
        (multivariateGaussian 0
          (twoSLSFunctionVariance
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R)) ∧
      TendstoInMeasure μ
        (fun t ω => twoSLSFunctionVHat
          (twoSLSVHatStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω))
          R)
        atTop
          (fun _ =>
            twoSLSFunctionVariance
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) R) :=
  twoSLSFunction_theorem12_5_of_textbook12_2_joint_iid_73_const_derivative
    (μ := μ) (q := q) (rfun := rfun)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h.toResidualTextbookFourthConditions h73

/-- Hansen Theorem 12.6 statistic-level wrapper: under the null-centered
restriction Gaussian limit and covariance consistency, the nonlinear 2SLS Wald
statistic converges to `χ²(q)`. -/
theorem twoSLSFunctionWaldStatOrZero_tendstoInDistribution_chiSquared
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {root : ℕ → ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {G : Ω' → EuclideanSpace ℝ (Fin r)}
    {Vtheta : Matrix (Fin r) (Fin r) ℝ}
    (hT : TendstoInDistribution
      (fun (t : ℕ) ω =>
        root t •
          (rfun (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) - θ0))
      atTop (fun ω i => (G ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hG : HasLaw G (multivariateGaussian 0 Vtheta) ν)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (t : ℕ) ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω))
      atTop (fun _ => Vtheta))
    (hV_posDef : Vtheta.PosDef) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) (root t))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  simpa [twoSLSFunctionWaldStatOrZero] using
    restrictionWaldStatOrZero_tendstoInDistribution_chiSquared
      (μ := μ) (ν := ν) (r := r)
      (T := fun t ω =>
        root t •
          (rfun (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) - θ0))
      (Z := G)
      (VthetaHat := fun t ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω))
      (Vtheta := Vtheta)
      hT hG hV_meas hV hV_posDef

/-- Hansen Theorem 12.6 calibrated-size wrapper: if the critical value has
upper-tail chi-square mass `α`, then the nonlinear 2SLS Wald rejection
probability tends to `α` under `H₀`. -/
theorem twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {root : ℕ → ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {G : Ω' → EuclideanSpace ℝ (Fin r)}
    {Vtheta : Matrix (Fin r) (Fin r) ℝ}
    (hT : TendstoInDistribution
      (fun (t : ℕ) ω =>
        root t •
          (rfun (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) - θ0))
      atTop (fun ω i => (G ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hG : HasLaw G (multivariateGaussian 0 Vtheta) ν)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (t : ℕ) ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω))
      atTop (fun _ => Vtheta))
    (hV_posDef : Vtheta.PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun t => μ {ω | crit <
        twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) (root t)})
      atTop (𝓝 alpha) := by
  have hW := twoSLSFunctionWaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (ν := ν) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (Y := Y) (root := root)
    (Rhat := Rhat) (Vhatβ := Vhatβ) (G := G) (Vtheta := Vtheta)
    hT hG hV_meas hV hV_posDef
  exact chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ)
    (W := fun t ω =>
      twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω) (root t))
    (q := r) (crit := crit) (alpha := alpha) hcrit hW

/-- Hansen Theorem 12.6 lower-tail critical-value convention: if
`P[χ²(q) ≤ c] = 1 - α`, then the nonlinear 2SLS Wald rejection probability
tends to `α` under `H₀`. -/
theorem twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {root : ℕ → ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {G : Ω' → EuclideanSpace ℝ (Fin r)}
    {Vtheta : Matrix (Fin r) (Fin r) ℝ}
    (hT : TendstoInDistribution
      (fun (t : ℕ) ω =>
        root t •
          (rfun (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) - θ0))
      atTop (fun ω i => (G ω : Fin r → ℝ) i) (fun _ => μ) ν)
    (hG : HasLaw G (multivariateGaussian 0 Vtheta) ν)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (t : ℕ) ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω))
      atTop (fun _ => Vtheta))
    (hV_posDef : Vtheta.PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    Tendsto
      (fun t => μ {ω | crit <
        twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) (root t)})
      atTop (𝓝 alpha) :=
  twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha
    (μ := μ) (ν := ν) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (Y := Y) (root := root)
    (Rhat := Rhat) (Vhatβ := Vhatβ) (G := G) (Vtheta := Vtheta)
    hT hG hV_meas hV hV_posDef
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6 from Theorem 12.5.**

Under the nonlinear null `r(β) = θ₀`, the Theorem 12.5 Gaussian limit and
plug-in covariance consistency imply the calibrated chi-square Wald rejection
probability tends to its nominal upper-tail probability. -/
theorem twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha_of_theorem12_5
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hnull : rfun β = θ0)
    (hlinearizationβ : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            (Real.sqrt (t : ℝ) •
              sampleCrossMoment (fun i : Fin t => Z i.val ω)
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0))
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hV_posDef : (twoSLSFunctionVariance Vβ R).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun t => μ {ω | crit <
        twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
      atTop (𝓝 alpha) := by
  let Vtheta : Matrix (Fin r) (Fin r) ℝ := twoSLSFunctionVariance Vβ R
  have h125 := twoSLSFunction_theorem12_5
    (μ := μ) (q := Fin r) (rfun := rfun) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
    hAN hVβ hlinearizationβ hβ_meas hrem hθ_meas hV_meas hR_meas hVhatβ hRhat
  have hTraw :=
    h125.1.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin r => ℝ))
  have hT : TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (rfun (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) - θ0))
      atTop (fun z : EuclideanSpace ℝ (Fin r) => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vtheta) := by
    simpa [Vtheta, Function.comp_def, twoSLSFunctionEstimatorOrZero_eq_star,
      twoSLSFunctionEstimator, hnull] using hTraw
  have hG : HasLaw
      (fun z : EuclideanSpace ℝ (Fin r) => z)
      (multivariateGaussian 0 Vtheta)
      (multivariateGaussian 0 Vtheta) := by
    simpa [id] using (HasLaw.id (μ := multivariateGaussian 0 Vtheta))
  have hVtheta_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω)) μ := by
    intro t
    have hRT_meas : AEStronglyMeasurable (fun ω => (Rhat t ω)ᵀ) μ :=
      (continuous_id.matrix_transpose).comp_aestronglyMeasurable (hR_meas t)
    have hleft : AEStronglyMeasurable
        (fun ω => (Rhat t ω)ᵀ * Vhatβ t ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hRT_meas.prodMk (hV_meas t))
    simpa [twoSLSFunctionVHat] using
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hleft.prodMk (hR_meas t))
  exact twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha
    (μ := μ) (ν := multivariateGaussian 0 Vtheta)
    (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (Y := Y)
    (root := fun n => Real.sqrt (n : ℝ))
    (Rhat := Rhat) (Vhatβ := Vhatβ)
    (G := fun z : EuclideanSpace ℝ (Fin r) => z)
    (Vtheta := Vtheta)
    hT hG hVtheta_meas (by simpa [Vtheta] using h125.2)
    (by simpa [Vtheta] using hV_posDef) hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6 from Theorem 12.5**, statistic form.

Under the nonlinear null `r(β) = θ₀`, the Theorem 12.5 Gaussian limit and
plug-in covariance consistency imply that the nonlinear 2SLS Wald statistic
itself converges to `χ²(q)`. -/
theorem twoSLSFunctionWaldStatOrZero_tendstoInDistribution_chiSquared_of_theorem12_5
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hnull : rfun β = θ0)
    (hlinearizationβ : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            (Real.sqrt (t : ℝ) •
              sampleCrossMoment (fun i : Fin t => Z i.val ω)
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0))
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hV_posDef : (twoSLSFunctionVariance Vβ R).PosDef) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  let Vtheta : Matrix (Fin r) (Fin r) ℝ := twoSLSFunctionVariance Vβ R
  have h125 := twoSLSFunction_theorem12_5
    (μ := μ) (q := Fin r) (rfun := rfun) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
    hAN hVβ hlinearizationβ hβ_meas hrem hθ_meas hV_meas hR_meas hVhatβ hRhat
  have hTraw :=
    h125.1.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin r => ℝ))
  have hT : TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (rfun (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) - θ0))
      atTop (fun z : EuclideanSpace ℝ (Fin r) => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vtheta) := by
    simpa [Vtheta, Function.comp_def, twoSLSFunctionEstimatorOrZero_eq_star,
      twoSLSFunctionEstimator, hnull] using hTraw
  have hG : HasLaw
      (fun z : EuclideanSpace ℝ (Fin r) => z)
      (multivariateGaussian 0 Vtheta)
      (multivariateGaussian 0 Vtheta) := by
    simpa [id] using (HasLaw.id (μ := multivariateGaussian 0 Vtheta))
  have hVtheta_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω)) μ := by
    intro t
    have hRT_meas : AEStronglyMeasurable (fun ω => (Rhat t ω)ᵀ) μ :=
      (continuous_id.matrix_transpose).comp_aestronglyMeasurable (hR_meas t)
    have hleft : AEStronglyMeasurable
        (fun ω => (Rhat t ω)ᵀ * Vhatβ t ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hRT_meas.prodMk (hV_meas t))
    simpa [twoSLSFunctionVHat] using
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hleft.prodMk (hR_meas t))
  exact twoSLSFunctionWaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (ν := multivariateGaussian 0 Vtheta)
    (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (Y := Y)
    (root := fun n => Real.sqrt (n : ℝ))
    (Rhat := Rhat) (Vhatβ := Vhatβ)
    (G := fun z : EuclideanSpace ℝ (Fin r) => z)
    (Vtheta := Vtheta)
    hT hG hVtheta_meas (by simpa [Vtheta] using h125.2)
    (by simpa [Vtheta] using hV_posDef)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6 from Theorem 12.5**, combined statistic and size
form. -/
theorem twoSLSFunctionWald_theorem12_6_of_theorem12_5
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hnull : rfun β = θ0)
    (hlinearizationβ : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            (Real.sqrt (t : ℝ) •
              sampleCrossMoment (fun i : Fin t => Z i.val ω)
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0))
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hV_posDef : (twoSLSFunctionVariance Vβ R).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  ⟨twoSLSFunctionWaldStatOrZero_tendstoInDistribution_chiSquared_of_theorem12_5
      (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
      hAN hVβ hnull hlinearizationβ hβ_meas hrem hθ_meas hV_meas hR_meas
      hVhatβ hRhat hV_posDef,
    twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha_of_theorem12_5
      (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
      hAN hVβ hnull hlinearizationβ hβ_meas hrem hθ_meas hV_meas hR_meas
      hVhatβ hRhat hV_posDef hcrit⟩

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, structural-model endpoint.

This wrapper reuses `twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha_of_theorem12_5`
and supplies the coefficient linearization from the exact scaled 2SLS identity. -/
theorem twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha_of_model_nonsingular
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hnull : rfun β = θ0)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hV_posDef : (twoSLSFunctionVariance Vβ R).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun t => μ {ω | crit <
        twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
      atTop (𝓝 alpha) :=
  twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha_of_theorem12_5
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
    hAN hVβ hnull
    (twoSLSBetaStar_sqrt_linearization_tendstoInMeasure_zero_of_model_nonsingular
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) β hmodel hunit)
    hβ_meas hrem hθ_meas hV_meas hR_meas hVhatβ hRhat hV_posDef hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, statistic-level structural endpoint.

Under the nonlinear null, the structural Theorem 12.5 endpoint implies that
the Wald statistic itself converges to `χ²(q)`. -/
theorem twoSLSFunctionWaldStatOrZero_tendstoInDistribution_chiSquared_of_model_nonsingular
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hnull : rfun β = θ0)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hV_posDef : (twoSLSFunctionVariance Vβ R).PosDef) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  let Vtheta : Matrix (Fin r) (Fin r) ℝ := twoSLSFunctionVariance Vβ R
  have h125 := twoSLSFunction_theorem12_5_of_model_nonsingular
    (μ := μ) (q := Fin r) (rfun := rfun) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
    hAN hVβ hmodel hunit hβ_meas hrem hθ_meas hV_meas hR_meas hVhatβ hRhat
  have hTraw :=
    h125.1.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : Fin r => ℝ))
  have hT : TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (rfun (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) - θ0))
      atTop (fun z : EuclideanSpace ℝ (Fin r) => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vtheta) := by
    simpa [Vtheta, Function.comp_def, twoSLSFunctionEstimatorOrZero_eq_star,
      twoSLSFunctionEstimator, hnull] using hTraw
  have hG : HasLaw
      (fun z : EuclideanSpace ℝ (Fin r) => z)
      (multivariateGaussian 0 Vtheta)
      (multivariateGaussian 0 Vtheta) := by
    simpa [id] using (HasLaw.id (μ := multivariateGaussian 0 Vtheta))
  have hVtheta_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω => twoSLSFunctionVHat (Vhatβ t ω) (Rhat t ω)) μ := by
    intro t
    have hRT_meas : AEStronglyMeasurable (fun ω => (Rhat t ω)ᵀ) μ :=
      (continuous_id.matrix_transpose).comp_aestronglyMeasurable (hR_meas t)
    have hleft : AEStronglyMeasurable
        (fun ω => (Rhat t ω)ᵀ * Vhatβ t ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hRT_meas.prodMk (hV_meas t))
    simpa [twoSLSFunctionVHat] using
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hleft.prodMk (hR_meas t))
  exact twoSLSFunctionWaldStatOrZero_tendstoInDistribution_chiSquared
    (μ := μ) (ν := multivariateGaussian 0 Vtheta)
    (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (Y := Y)
    (root := fun n => Real.sqrt (n : ℝ))
    (Rhat := Rhat) (Vhatβ := Vhatβ)
    (G := fun z : EuclideanSpace ℝ (Fin r) => z)
    (Vtheta := Vtheta)
    hT hG hVtheta_meas (by simpa [Vtheta] using h125.2)
    (by simpa [Vtheta] using hV_posDef)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, combined structural endpoint.

This returns both textbook conclusions: the Wald statistic converges to
`χ²(q)`, and the rejection probability at an upper-tail critical value tends to
the nominal size. -/
theorem twoSLSFunctionWald_theorem12_6_of_model_nonsingular
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hnull : rfun β = θ0)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hV_posDef : (twoSLSFunctionVariance Vβ R).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  ⟨twoSLSFunctionWaldStatOrZero_tendstoInDistribution_chiSquared_of_model_nonsingular
      (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
      hAN hVβ hnull hmodel hunit hβ_meas hrem hθ_meas hV_meas hR_meas
      hVhatβ hRhat hV_posDef,
    twoSLSFunctionWaldTest_rejectionProb_tendsto_alpha_of_model_nonsingular
      (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
      hAN hVβ hnull hmodel hunit hβ_meas hrem hθ_meas hV_meas hR_meas
      hVhatβ hRhat hV_posDef hcrit⟩

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, lower-tail critical-value convention.

This is the same combined structural endpoint as
`twoSLSFunctionWald_theorem12_6_of_model_nonsingular`, stated with Hansen's
usual critical-value convention `(χ²(q))(-∞, c] = 1 - α`. -/
theorem twoSLSFunctionWald_theorem12_6_of_model_nonsingular_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Vβ : Matrix k k ℝ} {R : Matrix k (Fin r) ℝ}
    {Vhatβ : ℕ → Ω → Matrix k k ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hVβ : Vβ.PosSemidef)
    (hnull : rfun β = θ0)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable (Vhatβ t) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hVhatβ : TendstoInMeasure μ Vhatβ atTop (fun _ => Vβ))
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hV_posDef : (twoSLSFunctionVariance Vβ R).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω) (Vhatβ t ω)
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_model_nonsingular
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (Vβ := Vβ) (R := R) (Vhatβ := Vhatβ) (Rhat := Rhat)
    hAN hVβ hnull hmodel hunit hβ_meas hrem hθ_meas hV_meas hR_meas
    hVhatβ hRhat hV_posDef
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, formula-facing 2SLS covariance endpoint.

This specializes the combined Wald endpoint to Hansen's displayed robust 2SLS
coefficient covariance `Vβ` and actual plug-in estimator `V̂β`. Positive
definiteness of the function covariance is derived from positive definiteness of
the coefficient covariance and full column rank of the derivative matrix. -/
theorem twoSLSFunctionWald_theorem12_6_of_covariance_formula
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSFormulaAsymptoticNormalConditions μ Z X e QXZ QZZ Omega QZX)
    (hVβ_posDef : (twoSLSAsymptoticVariance QXZ QZZ Omega QZX).PosDef)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β = θ0)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ Omega QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_model_nonsingular
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (Vβ := twoSLSAsymptoticVariance QXZ QZZ Omega QZX) (R := R)
    (Vhatβ := fun t ω =>
      twoSLSVHatStar
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω))
    (Rhat := Rhat)
    hAN hVβ_posDef.posSemidef hnull hmodel hunit hβ_meas hrem hθ_meas
    hV_meas hR_meas hcov.robust_tendsto hRhat
    (twoSLSFunctionVariance_posDef_of_cov_posDef
      (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) R hVβ_posDef hR_full)
    hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, formula-facing lower-tail critical-value convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_covariance_formula_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSFormulaAsymptoticNormalConditions μ Z X e QXZ QZZ Omega QZX)
    (hVβ_posDef : (twoSLSAsymptoticVariance QXZ QZZ Omega QZX).PosDef)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β = θ0)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ Omega QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_covariance_formula
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
    (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
    (sigma2 := sigma2) (R := R) (Rhat := Rhat)
    hAN hVβ_posDef hR_full hnull hcov hmodel hunit hβ_meas hrem hθ_meas
    hV_meas hR_meas hRhat
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, formula-facing 2SLS covariance endpoint with
coefficient-covariance positive definiteness derived from Hansen's population
rank and positivity assumptions. -/
theorem twoSLSFunctionWald_theorem12_6_of_covariance_formula_rank
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSFormulaAsymptoticNormalConditions μ Z X e QXZ QZZ Omega QZX)
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ : QZZ.PosDef)
    (hOmega : Omega.PosDef)
    (hQZX_full : Function.Injective QZX.mulVec)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β = θ0)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ Omega QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_covariance_formula
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
    (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
    (sigma2 := sigma2) (R := R) (Rhat := Rhat)
    hAN
    (twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
      QXZ QZZ Omega QZX hQXZ hQZZ hOmega hQZX_full)
    hR_full hnull hcov hmodel hunit hβ_meas hrem hθ_meas hV_meas
    hR_meas hRhat hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, lower-tail convention with coefficient-covariance
positive definiteness derived from Hansen's population rank and positivity
assumptions. -/
theorem twoSLSFunctionWald_theorem12_6_of_covariance_formula_rank_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hAN : TwoSLSFormulaAsymptoticNormalConditions μ Z X e QXZ QZZ Omega QZX)
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ : QZZ.PosDef)
    (hOmega : Omega.PosDef)
    (hQZX_full : Function.Injective QZX.mulVec)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β = θ0)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ Omega QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_covariance_formula_rank
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
    (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
    (sigma2 := sigma2) (R := R) (Rhat := Rhat)
    hAN hQXZ hQZZ hOmega hQZX_full hR_full hnull hcov hmodel hunit
    hβ_meas hrem hθ_meas hV_meas hR_meas hRhat
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, score-CLT/sample-moment constructor.

This is the common formula-facing endpoint where Hansen's middle matrix is the
instrument-score covariance `Ω = Var(eZ)`. It reuses the Chapter 12.2
sample-moment/score-CLT constructor and the formula-facing Wald endpoint. -/
theorem twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ)
    (hVβ_posDef :
      (twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX).PosDef)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β = θ0)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ (scoreCovMat μ Z e) QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_theorem12_5
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
    (Vβ := twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX)
    (R := R)
    (Vhatβ := fun t ω =>
      twoSLSVHatStar
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω))
    (Rhat := Rhat)
    (hMom.toFormulaAsymptoticNormalConditions hScore hQZZ_symm hQZX)
    hVβ_posDef.posSemidef hnull
    (twoSLSBetaStar_sqrt_linearization_tendstoInMeasure_zero_of_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) hMom β hmodel)
    hβ_meas hrem hθ_meas hV_meas hR_meas hcov.robust_tendsto hRhat
    (twoSLSFunctionVariance_posDef_of_cov_posDef
      (twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX) R
      hVβ_posDef hR_full)
    hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, score-CLT/sample-moment lower-tail convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ)
    (hVβ_posDef :
      (twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX).PosDef)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β = θ0)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ (scoreCovMat μ Z e) QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
    (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX)
    (sigma2 := sigma2) (R := R) (Rhat := Rhat)
    hMom hScore hQZZ_symm hQZX hVβ_posDef hR_full hnull hcov hmodel
    hβ_meas hrem hθ_meas hV_meas hR_meas hRhat
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, score-CLT/sample-moment endpoint with coefficient
covariance positive definiteness derived from `Q_ZZ > 0`, `Ω > 0`, and
full-column-rank `Q_ZX`. -/
theorem twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments_rank
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e)
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ : QZZ.PosDef)
    (hOmega : (scoreCovMat μ Z e).PosDef)
    (hQZX_full : Function.Injective QZX.mulVec)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β = θ0)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ (scoreCovMat μ Z e) QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) := by
  have hQZZ_symm : QZZᵀ = QZZ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hQZZ.1.eq
  have hQZX : QZX = QXZᵀ := by
    rw [hQXZ, Matrix.transpose_transpose]
  exact twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
    (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX)
    (sigma2 := sigma2) (R := R) (Rhat := Rhat)
    hMom hScore hQZZ_symm hQZX
    (twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
      QXZ QZZ (scoreCovMat μ Z e) QZX hQXZ hQZZ hOmega hQZX_full)
    hR_full hnull hcov hmodel hβ_meas hrem hθ_meas hV_meas hR_meas hRhat
    hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, score-CLT/sample-moment lower-tail endpoint with
coefficient covariance positive definiteness derived from Hansen's population
rank and positivity assumptions. -/
theorem twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments_rank_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e)
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ : QZZ.PosDef)
    (hOmega : (scoreCovMat μ Z e).PosDef)
    (hQZX_full : Function.Injective QZX.mulVec)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β = θ0)
    (hcov : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ (scoreCovMat μ Z e) QZX sigma2)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments_rank
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
    (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX)
    (sigma2 := sigma2) (R := R) (Rhat := Rhat)
    hMom hScore hQXZ hQZZ hOmega hQZX_full hR_full hnull hcov hmodel
    hβ_meas hrem hθ_meas hV_meas hR_meas hRhat
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, joint-iid Assumption 12.2 constructor.

This theorem composes the primitive single-row Assumption 12.2 package, the
Hansen Theorem 12.3 covariance constructor, and the rank-specialized Wald
endpoint. The remaining explicit inputs are the nonlinear Assumption-7.3
linearization and derivative-estimator convergence surface. -/
theorem twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_moments
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β0 = θ0)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β0))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) := by
  let hIid := h.toIidFourthConditions
  let hGram := hIid.toGramConditions
  let hMom := hGram.toTwoSLSAssumption12_1GramConditions.toSampleMomentConvergenceConditions
  have hQXZ :
      twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)) =
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ :=
    twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
      (μ := μ) (Z := Z) (X := X) hGram.toTwoSLSAssumption12_1GramConditions.combined_gram
  have hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0)) μ :=
    (twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β0 hmodel).forall_aemeasurable
  exact twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments_rank
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β0)
    (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
    (sigma2 := errorVariance μ e) (R := R) (Rhat := Rhat)
    hMom hGram.score_clt hQXZ h.qzz_posDef h.omega_posDef h.qzx_rank
    hR_full hnull
    (TwoSLSCovarianceFormulaConsistencyConditions.of_assumption12_2_joint_iid_moments
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β0 hmodel hOmegaCross hOmegaQuadratic hSigmaCross)
    hmodel hβ_meas hrem hθ_meas hV_meas hR_meas hRhat hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, joint-iid Assumption 12.2 lower-tail convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_moments_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β0 = θ0)
    (hrem : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ (Fin r))) -
        fun (t : ℕ) ω =>
          matrixContinuousLinearMap Rᵀ
            (WithLp.toLp 2
              (Real.sqrt (t : ℝ) •
                (twoSLSBetaStar
                  (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                  (fun i : Fin t => Y i.val ω) - β0))))
      atTop (fun _ => 0))
    (hθ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        (WithLp.toLp 2
          (Real.sqrt (t : ℝ) •
            (twoSLSFunctionEstimatorOrZero rfun
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω) - rfun β0)) :
          EuclideanSpace ℝ (Fin r))) μ)
    (hV_meas : ∀ t : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_moments
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rhat := Rhat)
    h β0 hmodel hOmegaCross hOmegaQuadratic hSigmaCross
    hR_full hnull hrem hθ_meas hV_meas hR_meas hRhat
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, joint-iid Assumption 12.2 plus Assumption 7.3.

This Hansen-facing smooth-Wald endpoint derives the nonlinear linearization from
Assumption 7.3 and Theorem 12.2. The Assumption 12.2 rank and positivity fields
discharge positive definiteness of the Wald covariance; the remaining
feasible-covariance and derivative-estimator obligations are collected in
`TwoSLSFunctionAssumption12_2JointIid73Conditions`. -/
theorem twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
by
  let hIid := h.toIidFourthConditions
  let hGram := hIid.toGramConditions
  let hMom := hGram.toTwoSLSAssumption12_1GramConditions.toSampleMomentConvergenceConditions
  have hQXZ :
      twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)) =
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ :=
    twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
      (μ := μ) (Z := Z) (X := X) hGram.toTwoSLSAssumption12_1GramConditions.combined_gram
  have hβ_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0)) μ :=
    (twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β0 hmodel).forall_aemeasurable
  let hcov : TwoSLSCovarianceFormulaConsistencyConditions μ Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) :=
    TwoSLSCovarianceFormulaConsistencyConditions.of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h.toIidFourthConditions β0 hmodel hc.covariance_weights
  exact twoSLSFunctionWald_theorem12_6_of_scoreCLT_sample_moments_rank
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (β := β0)
    (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
    (sigma2 := errorVariance μ e) (R := R) (Rhat := Rhat)
    hMom hGram.score_clt hQXZ h.qzz_posDef h.omega_posDef h.qzx_rank
    hR_full hnull hcov hmodel hβ_meas
    (twoSLSFunction_remainder_tendstoInMeasure_of_assumption12_2_joint_iid_73_model
      (μ := μ) (rfun := rfun) (Z := Z) (X := X) (e := e) (Y := Y)
      (β0 := β0) (R := R) h hmodel h73 hc.theta_aemeasurable)
    hc.theta_aemeasurable
    hc.covariance_aestronglyMeasurable
    hc.derivative_aestronglyMeasurable hc.derivative_tendsto hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, joint-iid Assumption 12.2 plus Assumption 7.3,
lower-tail critical-value convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat)
    (hR_full : Function.Injective R.mulVec)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rhat := Rhat)
    h β0 hmodel h73 hc hR_full hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, joint-iid Assumption 12.2 plus Assumption 7.3,
with the derivative full-rank condition read directly from `SmoothFunctionAssumption73`. -/
theorem twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model_fullRank
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rhat := Rhat)
    h β0 hmodel h73 hc h73.fullRank hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, joint-iid Assumption 12.2 plus Assumption 7.3,
lower-tail convention, with derivative full rank read from `SmoothFunctionAssumption73`. -/
theorem twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model_fullRank_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model_fullRank
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rhat := Rhat)
    h β0 hmodel h73 hc hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, primitive joint-iid Assumption 12.2 plus
Assumption 7.3.

This theorem-facing wrapper derives the function/covariance condition package
from primitive joint-iid Assumption 12.2, measurability of `r`, and the mixed
moment hypotheses used by the Chapter 12 covariance constructor. The chi-square
Wald limit and calibrated-size conclusion are unchanged from the packaged
Theorem 12.6 endpoint. -/
theorem twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moments_measurable
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) := by
  let hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R Rhat :=
    TwoSLSFunctionAssumption12_2JointIid73Conditions.of_joint_iid_mixed_moments_measurable
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (rfun := rfun) (β0 := β0) (R := R) (Rhat := Rhat)
      hrfun h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR_meas hRhat
  exact
    twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model_fullRank
      (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (Rhat := Rhat)
      h β0 hmodel h73 hc hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, primitive joint-iid Assumption 12.2 plus
Assumption 7.3, lower-tail critical-value convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moments_measurable_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moments_measurable
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rhat := Rhat)
    hrfun h β0 hmodel h73 hOmegaCross hOmegaQuadratic hSigmaCross
    hR_meas hRhat hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, primitive joint-iid Assumption 12.2 plus
Assumption 7.3, with the plug-in derivative fixed at Hansen's derivative
matrix `R`. -/
theorem twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moments_measurable_const_derivative
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) := by
  let hc : TwoSLSFunctionAssumption12_2JointIid73Conditions
      μ Z X e Y rfun β0 R (fun _ _ => R) :=
    TwoSLSFunctionAssumption12_2JointIid73Conditions.of_joint_iid_mixed_moments_measurable_const_derivative
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (rfun := rfun) (β0 := β0) (R := R)
      hrfun h hmodel hOmegaCross hOmegaQuadratic hSigmaCross
  exact
    twoSLSFunctionWald_theorem12_6_of_assumption12_2_joint_iid_73_model_fullRank
      (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (Rhat := fun _ _ => R)
      h β0 hmodel h73 hc hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, primitive joint-iid Assumption 12.2 plus
Assumption 7.3, deterministic derivative, lower-tail critical-value
convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moments_measurable_const_derivative_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moments_measurable_const_derivative
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h β0 hmodel h73 hOmegaCross hOmegaQuadratic hSigmaCross
    hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

/-- **Hansen Theorem 12.6**, packaged Assumption 12.2 mixed-moment route.

This wrapper consumes the same canonical mixed-moment Assumption 12.2 package as
Theorem 12.3, then delegates to the primitive mixed-moment Wald endpoint. -/
theorem twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moments_measurable
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rhat := Rhat)
    hrfun h.toTwoSLSAssumption12_2JointIidFourthConditions β0 hmodel h73
    h.omega_cross_integrable h.omega_quadratic_integrable
    h.sigma_cross_integrable hR_meas hRhat hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, packaged Assumption 12.2 mixed-moment route with
Hansen's plug-in derivative estimator
`Rhat = ∂r(βhat₂SLS)'/∂β`.

The Wald statistic and size conclusion are exactly the arbitrary-`Rhat` theorem
specialized to the derivative map evaluated at the textbook-facing 2SLS
estimator. -/
theorem
    twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_derivativePlugIn
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rfun : (k → ℝ) → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) := by
  let Rhat : ℕ → Ω → Matrix k (Fin r) ℝ := fun t ω =>
    Rfun
      (twoSLSBetaOrZero
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω))
  let h12_2 : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e :=
    h.toTwoSLSAssumption12_2JointIidFourthConditions
  let h12_1 : TwoSLSAssumption12_1JointIidConditions μ Z X e :=
    h12_2.toTwoSLSAssumption12_1JointIidConditions
  have hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ :=
    SmoothFunctionPlugInDerivative73.twoSLSDerivativePlugIn_aestronglyMeasurable_of_assumption12_1_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h12_1 hmodel h73
  have hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R) :=
    SmoothFunctionPlugInDerivative73.twoSLSDerivativePlugIn_tendstoInMeasure_of_assumption12_1_joint_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h12_1 hmodel h73
  simpa [Rhat] using
    twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable
      (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
      (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (Rhat := Rhat)
      h73.function_measurable h β0 hmodel h73.toSmoothFunctionAssumption73
      hR_meas hRhat hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, packaged Assumption 12.2 mixed-moment route with
Hansen's plug-in derivative estimator and lower-tail critical-value convention. -/
theorem
    twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_derivativePlugIn_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rfun : (k → ℝ) → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_derivativePlugIn
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rfun := Rfun)
    h β0 hmodel h73 hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, literal joint-iid Assumption 12.2 plus
Assumption 7.3 with Hansen's plug-in derivative estimator
`Rhat = ∂r(βhat₂SLS)'/∂β`.

This endpoint hides the residual-substitution mixed moments behind Hansen's
finite-fourth-moment assumptions and states the Wald statistic and asymptotic
size conclusion directly. -/
theorem twoSLSFunctionWald_theorem12_6_of_textbook12_2_joint_iid_73_derivativePlugIn
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rfun : (k → ℝ) → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_derivativePlugIn
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rfun := Rfun)
    h.toJointIidMixedMomentConditions β0 h.model h73 hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, literal joint-iid Assumption 12.2 plus
Assumption 7.3 with Hansen's lower-tail critical-value convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_textbook12_2_joint_iid_73_derivativePlugIn_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rfun : (k → ℝ) → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_textbook12_2_joint_iid_73_derivativePlugIn
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rfun := Rfun)
    h h73 hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

/-- **Hansen Theorem 12.6**, packaged Assumption 12.2 mixed-moment route with
Hansen's lower-tail critical-value convention. -/
theorem
    twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rhat : ℕ → Ω → Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hR_meas : ∀ t : ℕ, AEStronglyMeasurable (Rhat t) μ)
    (hRhat : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 (Rhat t ω)
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rhat := Rhat)
    hrfun h β0 hmodel h73 hR_meas hRhat hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, packaged Assumption 12.2 mixed-moment route with
the derivative fixed at Hansen's matrix `R`. -/
theorem
    twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_const_derivative
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moments_measurable_const_derivative
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h.toTwoSLSAssumption12_2JointIidFourthConditions β0 hmodel h73
    h.omega_cross_integrable h.omega_quadratic_integrable
    h.sigma_cross_integrable hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, packaged Assumption 12.2 mixed-moment route with
deterministic derivative and lower-tail critical-value convention. -/
theorem
    twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_const_derivative_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β0 : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_const_derivative
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h β0 hmodel h73 hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, literal joint-iid Assumption 12.2 plus
Assumption 7.3 and `H₀`, with Hansen's derivative matrix fixed at `R`.

This is the deterministic-derivative counterpart to the preferred plug-in
derivative theorem-facing endpoint. It derives the mixed-moment covariance
premises from Hansen's finite-fourth Assumption 12.2 package and returns the
same chi-square limit and upper-tail size conclusion. -/
theorem twoSLSFunctionWald_theorem12_6_of_textbook12_2_joint_iid_73_const_derivative
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_joint_iid_73_mixed_moment_conditions_measurable_const_derivative
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h.toJointIidMixedMomentConditions β0 h.model h73 hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, literal joint-iid Assumption 12.2 plus
Assumption 7.3 and `H₀`, deterministic derivative, and Hansen's lower-tail
critical-value convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_textbook12_2_joint_iid_73_const_derivative_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_textbook12_2_joint_iid_73_const_derivative
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h h73 hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, literal observed-row iid Assumption 12.2 plus
Assumption 7.3 with Hansen's plug-in derivative estimator. -/
theorem twoSLSFunctionWald_theorem12_6_of_textbook12_2_observed_iid_73_derivativePlugIn
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rfun : (k → ℝ) → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_textbook12_2_joint_iid_73_derivativePlugIn
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rfun := Rfun)
    h.toResidualTextbookFourthConditions h73 hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, literal observed-row iid Assumption 12.2 plus
Assumption 7.3 with Hansen's lower-tail critical-value convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_textbook12_2_observed_iid_73_derivativePlugIn_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    {R : Matrix k (Fin r) ℝ}
    {Rfun : (k → ℝ) → Matrix k (Fin r) ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionPlugInDerivative73 rfun β0 R Rfun)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0
            (Rfun
              (twoSLSBetaOrZero
                (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
                (fun i : Fin t => Y i.val ω)))
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_textbook12_2_observed_iid_73_derivativePlugIn
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (Rfun := Rfun)
    h h73 hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, literal observed-row iid Assumption 12.2 plus
Assumption 7.3 and `H₀`, with Hansen's derivative matrix fixed at `R`. -/
theorem twoSLSFunctionWald_theorem12_6_of_textbook12_2_observed_iid_73_const_derivative
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_textbook12_2_joint_iid_73_const_derivative
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h.toResidualTextbookFourthConditions h73 hnull hcrit

set_option linter.style.longLine false in
/-- **Hansen Theorem 12.6**, literal observed-row iid Assumption 12.2 plus
Assumption 7.3 and `H₀`, deterministic derivative, and lower-tail convention. -/
theorem twoSLSFunctionWald_theorem12_6_of_textbook12_2_observed_iid_73_const_derivative_lowerTail
    {r : ℕ} [Fact (0 < r)]
    {rfun : (k → ℝ) → (Fin r → ℝ)} {θ0 : Fin r → ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ} {R : Matrix k (Fin r) ℝ}
    (hrfun : Measurable rfun)
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β0)
    (h73 : SmoothFunctionAssumption73 rfun β0 R)
    (hnull : rfun β0 = θ0)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared r) (Set.Iic crit) = 1 - alpha) :
    TendstoInDistribution
        (fun (t : ℕ) ω =>
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) ∧
      Tendsto
        (fun t => μ {ω | crit <
          twoSLSFunctionWaldStatOrZero rfun θ0 R
            (twoSLSVHatStar
              (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
              (fun i : Fin t => Y i.val ω))
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) (Real.sqrt (t : ℝ))})
        atTop (𝓝 alpha) :=
  twoSLSFunctionWald_theorem12_6_of_textbook12_2_observed_iid_73_const_derivative
    (μ := μ) (r := r) (rfun := rfun) (θ0 := θ0)
    (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    hrfun h h73 hnull
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := r) (c := crit) (alpha := alpha) halpha_le_one hcrit)

end Normality

end HansenEconometrics
