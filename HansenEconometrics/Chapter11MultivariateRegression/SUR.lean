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

omit [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Weighted SUR score mean `n⁻¹∑ Xᵢ'W Yᵢ`, where `W` is typically
`Σ̂⁻¹` or `Σ⁻¹`. -/
noncomputable def surWeightedScoreMean
    (X : n → Matrix m k ℝ) (W : Matrix m m ℝ) (Y : n → m → ℝ) : k → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, (X i)ᵀ *ᵥ (W *ᵥ Y i)

omit [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Hansen feasible SUR estimator written at the observation-system level:
`(n⁻¹∑ Xᵢ'W Xᵢ)⁻¹ (n⁻¹∑ Xᵢ'W Yᵢ)`. -/
noncomputable def surBetaFromInverseCovStar
    (X : n → Matrix m k ℝ) (W : Matrix m m ℝ) (Y : n → m → ℝ) : k → ℝ :=
  (systemHomoskedasticMiddle X W)⁻¹ *ᵥ surWeightedScoreMean X W Y

omit [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Weighted SUR scores split into information matrix times coefficient plus weighted
error score under the system linear model. -/
theorem surWeightedScoreMean_outcomes_linear_model
    (X : n → Matrix m k ℝ) (W : Matrix m m ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) :
    surWeightedScoreMean X W Y =
      systemHomoskedasticMiddle X W *ᵥ β + surWeightedScoreMean X W e := by
  unfold surWeightedScoreMean systemHomoskedasticMiddle systemMiddleTerm
  rw [Matrix.smul_mulVec, ← smul_add]
  congr 1
  rw [Matrix.sum_mulVec, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hyi : Y i = X i *ᵥ β + e i := by
    ext j
    simp [Matrix.mulVec, dotProduct, hmodel i j]
  rw [hyi, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

omit [DecidableEq n] [DecidableEq m] in
/-- SUR estimator error identity with a fixed inverse-covariance weight. The right
side is exactly the totalized singular-information remainder. -/
theorem surBetaFromInverseCovStar_sub_identity
    (X : n → Matrix m k ℝ) (W : Matrix m m ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) :
    surBetaFromInverseCovStar X W Y - β -
        (systemHomoskedasticMiddle X W)⁻¹ *ᵥ surWeightedScoreMean X W e =
      ((systemHomoskedasticMiddle X W)⁻¹ * systemHomoskedasticMiddle X W - 1) *ᵥ β := by
  unfold surBetaFromInverseCovStar
  rw [surWeightedScoreMean_outcomes_linear_model X W e Y β hmodel,
      Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

omit [DecidableEq n] in
/-- Hansen residual covariance estimator `n⁻¹∑ êᵢêᵢ'`, reused by feasible SUR. -/
noncomputable def surResidualCovariance (ehat : n → m → ℝ) : Matrix m m ℝ :=
  systemSigmaHat ehat

omit [DecidableEq n] in
/-- Feasible SUR residual covariance using the totalized observation-level system residuals. -/
noncomputable def surResidualCovarianceStarObs
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) : Matrix m m ℝ :=
  surResidualCovariance (systemResidualStarObs X Y)

omit [DecidableEq n] [DecidableEq m] in
/-- The feasible SUR residual covariance is the same concrete residual covariance
used by the Chapter 11 system covariance estimator. -/
@[simp]
theorem surResidualCovarianceStarObs_eq_systemSigmaHatStarObs
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) :
    surResidualCovarianceStarObs X Y = systemSigmaHatStarObs X Y :=
  rfl

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

omit [DecidableEq n] [DecidableEq m] in
/-- Fixed-weight SUR score CLT package for Hansen Theorem 11.4.

For a fixed inverse-covariance weight `W`, the sample information matrix is
`n⁻¹∑ Xᵢ' W Xᵢ` and the score is `n⁻¹∑ Xᵢ' W eᵢ`. Under homoskedasticity with
`W = Σ⁻¹`, the score covariance is the same population information matrix `M`,
which yields the Hansen SUR covariance `M⁻¹`. -/
structure SURScoreCLTConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (W : Matrix m m ℝ)
    (e : ℕ → Ω → m → ℝ) (M : Matrix k k ℝ) : Prop where
  information_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) W) μ
  information_tendsto : TendstoInMeasure μ
    (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) W)
    atTop (fun _ => M)
  information_nonsing : IsUnit M.det
  information_inv_transpose : (M⁻¹)ᵀ = M⁻¹
  information_posSemidef : M.PosSemidef
  score_limit : TendstoInDistribution
    (fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        surWeightedScoreMean (fun i : Fin t => X i.val ω) W
          (fun i : Fin t => e i.val ω))
    atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
    (multivariateGaussian 0 M)

omit [DecidableEq n] [DecidableEq m] in
/-- Fixed-weight SUR linearized score CLT.

If the information matrix converges to nonsingular `M` and the fixed-weight
SUR score has covariance `M`, then the linearized statistic has Hansen
covariance `M⁻¹`. -/
theorem surLinearizedScore_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {W : Matrix m m ℝ} {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X W e M) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹ *ᵥ
          (Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) W
              (fun i : Fin t => e i.val ω)))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (surAsymptoticVariance M)) := by
  have hMinv : TendstoInMeasure μ
      (fun (t : ℕ) ω =>
        (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹)
      atTop (fun _ => M⁻¹) :=
    tendstoInMeasure_matrix_inv h.information_meas h.information_tendsto
      (fun _ => h.information_nonsing)
  have hMinv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => (systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) W)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.information_meas n)
  have hlin :=
    randomMatrix_mulVec_tendstoInDistribution_multivariateGaussian
      (Ahat := fun (t : ℕ) ω =>
        (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹)
      (A := M⁻¹) (S := M)
      (T := fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω) W
            (fun i : Fin t => e i.val ω))
      h.information_posSemidef hMinv_meas hMinv h.score_limit
  have hcov : M⁻¹ * M * (M⁻¹)ᵀ = surAsymptoticVariance M := by
    calc
      M⁻¹ * M * (M⁻¹)ᵀ = (M⁻¹ * M) * M⁻¹ := by
        rw [h.information_inv_transpose]
      _ = 1 * M⁻¹ := by rw [Matrix.nonsing_inv_mul M h.information_nonsing]
      _ = surAsymptoticVariance M := by simp [surAsymptoticVariance]
  simpa [hcov] using hlin

omit [DecidableEq n] [DecidableEq m] in
/-- The fixed-weight SUR sample information matrix is singular with asymptotically
vanishing probability whenever it converges to nonsingular `M`. -/
theorem measure_surInformation_singular_tendsto_zero
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {W : Matrix m m ℝ} {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X W e M) :
    Tendsto
      (fun n => μ {ω |
        ¬ IsUnit (systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) W).det})
      atTop (𝓝 0) := by
  have hDet : TendstoInMeasure μ
      (fun n ω => (systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) W).det)
      atTop (fun _ => M.det) :=
    tendstoInMeasure_continuous_comp h.information_meas h.information_tendsto
      (Continuous.matrix_det continuous_id)
  have hqne : M.det ≠ 0 := h.information_nonsing.ne_zero
  set ε : ℝ := |M.det| / 2 with hε_def
  have hε_pos : 0 < ε := half_pos (abs_pos.mpr hqne)
  have hε_le : ε ≤ |M.det| := by
    rw [hε_def]
    linarith [abs_nonneg M.det]
  have hmeas_eps := hDet (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas_eps
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero, not_not] at hω
  simp only [Set.mem_setOf_eq, hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
  exact ENNReal.ofReal_le_ofReal hε_le

omit [DecidableEq n] [DecidableEq m] in
/-- Exact fixed-weight SUR Star-estimator linearization on nonsingular sample
information matrices. -/
theorem surBetaFromInverseCovStar_linearization_of_nonsingular
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (W : Matrix m m ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hMhat_unit : ∀ t ω,
      IsUnit (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W).det) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω) W
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  have hzero :
      TendstoInMeasure μ (fun _ : ℕ => fun _ : Ω => (0 : k → ℝ)) atTop
        (fun _ => 0) := by
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ (fun _ => tendsto_const_nhds))
  refine TendstoInMeasure.congr (fun t => ?_) EventuallyEq.rfl hzero
  filter_upwards with ω
  let Xt : Fin t → Matrix m k ℝ := fun i => X i.val ω
  let et : Fin t → m → ℝ := fun i => e i.val ω
  let Yt : Fin t → m → ℝ := fun i => Y i.val ω
  let Mhat : Matrix k k ℝ := systemHomoskedasticMiddle Xt W
  let ghat : k → ℝ := surWeightedScoreMean Xt W et
  let betaHat : k → ℝ := surBetaFromInverseCovStar Xt W Yt
  have hid :
      betaHat - β - Mhat⁻¹ *ᵥ ghat =
        (Mhat⁻¹ * Mhat - 1) *ᵥ β := by
    simpa [betaHat, Mhat, ghat, Xt, et, Yt] using
      surBetaFromInverseCovStar_sub_identity
        (X := Xt) (W := W) (e := et) (Y := Yt) (β := β)
        (by intro i j; exact hmodel i.val ω j)
  have hlin0 : betaHat - β - Mhat⁻¹ *ᵥ ghat = 0 := by
    rw [hid, Matrix.nonsing_inv_mul Mhat (by simpa [Mhat, Xt] using hMhat_unit t ω)]
    simp
  ext a
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  have hcoord := congrArg (fun v : k → ℝ => v a) hlin0
  simp only [Pi.sub_apply, Pi.zero_apply] at hcoord
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply]
  symm
  change Real.sqrt (t : ℝ) * (betaHat a - β a) -
      Real.sqrt (t : ℝ) * (Mhat⁻¹ *ᵥ ghat) a = 0
  calc
    Real.sqrt (t : ℝ) * (betaHat a - β a) -
        Real.sqrt (t : ℝ) * (Mhat⁻¹ *ᵥ ghat) a =
          Real.sqrt (t : ℝ) *
            (betaHat a - β a - (Mhat⁻¹ *ᵥ ghat) a) := by ring
    _ = 0 := by rw [hcoord, mul_zero]

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen Theorem 11.4 fixed-weight SUR wrapper under explicit sample
nonsingularity. -/
theorem surBetaFromInverseCovStar_tendstoInDistribution_of_nonsingular
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {W : Matrix m m ℝ} {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X W e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hMhat_unit : ∀ t ω,
      IsUnit (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W).det)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (surAsymptoticVariance M)) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (t : ℕ) ω =>
      (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹ *ᵥ
        (Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω) W
            (fun i : Fin t => e i.val ω)))
    (Y := fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (surBetaFromInverseCovStar
          (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β))
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    (surLinearizedScore_tendstoInDistribution (μ := μ) h)
    (surBetaFromInverseCovStar_linearization_of_nonsingular
      (μ := μ) (X := X) (e := e) (Y := Y) W β hmodel hMhat_unit)
    hmeas

omit [DecidableEq n] [DecidableEq m] in
/-- Exact fixed-weight SUR Star-estimator linearization with the singular
information-matrix remainder handled by a high-probability argument. -/
theorem surBetaFromInverseCovStar_linearization
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {W : Matrix m m ℝ} {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X W e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω) W
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  have hsingular := measure_surInformation_singular_tendsto_zero h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun t => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  let Xt : Fin t → Matrix m k ℝ := fun i => X i.val ω
  let et : Fin t → m → ℝ := fun i => e i.val ω
  let Yt : Fin t → m → ℝ := fun i => Y i.val ω
  let Mhat : Matrix k k ℝ := systemHomoskedasticMiddle Xt W
  let ghat : k → ℝ := surWeightedScoreMean Xt W et
  let betaHat : k → ℝ := surBetaFromInverseCovStar Xt W Yt
  have hid :
      betaHat - β - Mhat⁻¹ *ᵥ ghat =
        (Mhat⁻¹ * Mhat - 1) *ᵥ β := by
    simpa [betaHat, Mhat, ghat, Xt, et, Yt] using
      surBetaFromInverseCovStar_sub_identity
        (X := Xt) (W := W) (e := et) (Y := Yt) (β := β)
        (by intro i j; exact hmodel i.val ω j)
  have hlin0 : betaHat - β - Mhat⁻¹ *ᵥ ghat = 0 := by
    rw [hid, Matrix.nonsing_inv_mul Mhat (by simpa [Mhat, Xt] using hunit)]
    simp
  have hzero :
      Real.sqrt (t : ℝ) • (betaHat - β) -
        Mhat⁻¹ *ᵥ (Real.sqrt (t : ℝ) • ghat) = 0 := by
    rw [Matrix.mulVec_smul, ← smul_sub, hlin0, smul_zero]
  change ε ≤ edist
    (((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω) W
                (fun i : Fin t => e i.val ω)))
        t ω) 0 at hω
  have hω0 : ε = 0 := by
    simpa [Xt, et, Yt, Mhat, ghat, betaHat, hzero] using hω
  exact hε.ne' hω0

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen Theorem 11.4 fixed-weight SUR wrapper with sample singularity handled
by the totalized Star estimator and high-probability information argument. -/
theorem surBetaFromInverseCovStar_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {W : Matrix m m ℝ} {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X W e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (surAsymptoticVariance M)) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (t : ℕ) ω =>
      (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹ *ᵥ
        (Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω) W
            (fun i : Fin t => e i.val ω)))
    (Y := fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (surBetaFromInverseCovStar
          (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β))
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    (surLinearizedScore_tendstoInDistribution (μ := μ) h)
    (surBetaFromInverseCovStar_linearization
      (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel)
    hmeas

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

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Hansen Theorem 11.5 finite-dimensional SUR efficiency comparison.

The OLS covariance surface `olsConditionalVarianceMatrix X Ωmat` dominates
the SUR/GLS covariance `(XᵀΩ⁻¹X)⁻¹` in positive-semidefinite order. This is
the Chapter 11 textbook comparison obtained by instantiating the Chapter 4
generalized Gauss-Markov theorem with the OLS linear estimator
`A = X (XᵀX)⁻¹`. -/
theorem sur_efficiency_vs_olsConditionalVarianceMatrix
    (X : Matrix n k ℝ) (Ωmat : Matrix n n ℝ)
    [Invertible Ωmat] [Invertible (Xᵀ * ⅟Ωmat * X)] [Invertible (Xᵀ * X)]
    (hΩ : Ωmat.PosSemidef) :
    (olsConditionalVarianceMatrix X Ωmat -
      surAsymptoticVariance (Xᵀ * ⅟Ωmat * X)).PosSemidef := by
  let A : Matrix n k ℝ := X * ⅟ (Xᵀ * X)
  have hAX : Aᵀ * X = (1 : Matrix k k ℝ) := by
    dsimp [A]
    calc
      (X * ⅟ (Xᵀ * X))ᵀ * X =
          ⅟ (Xᵀ * X) * (Xᵀ * X) := by
            rw [Matrix.transpose_mul, inv_gram_transpose]
            simp [Matrix.mul_assoc]
      _ = 1 := by rw [invOf_mul_self]
  have hgap := sur_efficiency_from_gls_variance_gap
    (X := X) (A := A) (Ωmat := Ωmat) hΩ hAX
  simpa [A, olsConditionalVarianceMatrix, invOf_eq_nonsing_inv,
    Matrix.transpose_nonsing_inv, gram_transpose, Matrix.mul_assoc] using hgap

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Population version of Hansen's system middle matrix:
`E[X_i' Σ X_i]`.

This is used by the population-efficiency surface for Theorem 11.5. -/
noncomputable def systemPopulationMiddle
    (μ : Measure Ω) (X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ) :
    Matrix k k ℝ :=
  ∫ ω, systemMiddleTerm (X ω) Sigma ∂μ

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Quadratic form of the population system middle matrix. -/
theorem systemPopulationMiddle_quadratic_eq_integral
    (X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma) μ)
    (a : k → ℝ) :
    a ⬝ᵥ (systemPopulationMiddle μ X Sigma *ᵥ a) =
      ∫ ω, (X ω *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X ω *ᵥ a)) ∂μ := by
  calc
    a ⬝ᵥ (systemPopulationMiddle μ X Sigma *ᵥ a)
        = ∑ i, ∑ j, a i * ((systemPopulationMiddle μ X Sigma) i j * a j) := by
          simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ = ∑ i, ∑ j,
          a i * ((∫ ω, (systemMiddleTerm (X ω) Sigma) i j ∂μ) * a j) := by
          congr
          ext i
          congr
          ext j
          have hentry := integral_apply_apply (μ := μ)
            (f := fun ω => systemMiddleTerm (X ω) Sigma) hX i j
          simpa [systemPopulationMiddle] using
            congrArg (fun z => a i * (z * a j)) hentry
    _ = ∑ i, ∑ j,
          ∫ ω, a i * ((systemMiddleTerm (X ω) Sigma) i j * a j) ∂μ := by
          congr
          ext i
          congr
          ext j
          rw [integral_const_mul]
          rw [integral_mul_const]
    _ = ∫ ω, ∑ i, ∑ j,
          a i * ((systemMiddleTerm (X ω) Sigma) i j * a j) ∂μ := by
          rw [integral_finset_sum]
          · congr
            ext i
            rw [integral_finset_sum]
            intro j hj
            simpa [mul_assoc] using
              ((Integrable.eval (Integrable.eval hX i) j).const_mul (a i)).mul_const (a j)
          · intro i hi
            exact integrable_finset_sum _ fun j hj => by
              simpa [mul_assoc] using
                ((Integrable.eval (Integrable.eval hX i) j).const_mul (a i)).mul_const (a j)
    _ = ∫ ω, (X ω *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X ω *ᵥ a)) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          have halg :
              a ⬝ᵥ (systemMiddleTerm (X ω) Sigma *ᵥ a) =
                (X ω *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X ω *ᵥ a)) := by
            calc
              a ⬝ᵥ (systemMiddleTerm (X ω) Sigma *ᵥ a)
                  = a ⬝ᵥ (((X ω)ᵀ * Sigma) *ᵥ (X ω *ᵥ a)) := by
                    rw [systemMiddleTerm, Matrix.mulVec_mulVec]
              _ = a ᵥ* ((X ω)ᵀ * Sigma) ⬝ᵥ (X ω *ᵥ a) := by
                    rw [Matrix.dotProduct_mulVec]
              _ = (X ω *ᵥ a) ᵥ* Sigma ⬝ᵥ (X ω *ᵥ a) := by
                    rw [← Matrix.vecMul_mulVec]
              _ = (X ω *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X ω *ᵥ a)) := by
                    rw [← Matrix.dotProduct_mulVec]
          simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using halg

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Population system middle matrices preserve positive semidefiniteness. -/
theorem systemPopulationMiddle_posSemidef
    (X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma) μ)
    (hSigma : Sigma.PosSemidef) :
    (systemPopulationMiddle μ X Sigma).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian]
    ext i j
    have hSigma_symm : Sigmaᵀ = Sigma := by
      simpa [Matrix.IsHermitian] using hSigma.1.eq
    calc
      (systemPopulationMiddle μ X Sigma) j i
          = ∫ ω, (systemMiddleTerm (X ω) Sigma) j i ∂μ := by
            exact integral_apply_apply (μ := μ)
              (f := fun ω => systemMiddleTerm (X ω) Sigma) hX j i
      _ = ∫ ω, (systemMiddleTerm (X ω) Sigma) i j ∂μ := by
            congr with ω
            have hterm :
                (systemMiddleTerm (X ω) Sigma)ᵀ =
                  systemMiddleTerm (X ω) Sigma := by
              unfold systemMiddleTerm
              rw [Matrix.transpose_mul, Matrix.transpose_mul,
                Matrix.transpose_transpose, hSigma_symm]
              simp [Matrix.mul_assoc]
            exact congrFun (congrFun hterm i) j
      _ = (systemPopulationMiddle μ X Sigma) i j := by
            exact (integral_apply_apply (μ := μ)
              (f := fun ω => systemMiddleTerm (X ω) Sigma) hX i j).symm
  · intro a
    change 0 ≤ a ⬝ᵥ (systemPopulationMiddle μ X Sigma *ᵥ a)
    rw [systemPopulationMiddle_quadratic_eq_integral X Sigma hX a]
    exact integral_nonneg fun ω => by
      simpa using Matrix.PosSemidef.dotProduct_mulVec_nonneg hSigma (X ω *ᵥ a)

omit [IsProbabilityMeasure μ] [DecidableEq m] in
/-- Population Gauss-Markov variance-gap certificate.

This is the Hilbert-space analogue of the deterministic Chapter 4 variance-gap
identity used by Hansen Theorem 11.5. Once the population variance gap has been
expanded as an expected quadratic middle, positive semidefiniteness follows
from the positive semidefiniteness of the error covariance matrix. -/
theorem population_generalizedGaussMarkov_variance_gap_posSemidef_of_expansion
    (V M : Matrix k k ℝ) (B : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hB : Integrable (fun ω => systemMiddleTerm (B ω) Sigma) μ)
    (hSigma : Sigma.PosSemidef)
    (hgap : V - M⁻¹ = systemPopulationMiddle μ B Sigma) :
    (V - M⁻¹).PosSemidef := by
  rw [hgap]
  exact systemPopulationMiddle_posSemidef B Sigma hB hSigma

omit [IsProbabilityMeasure μ] [DecidableEq m] in
/-- Hansen Theorem 11.5 population-moment SUR efficiency wrapper.

The conclusion is Hansen's population Loewner comparison. The premise `hgap`
is the exact population Gauss-Markov expansion of the variance gap as
`E[B_i'ΣB_i]`, with
`B_i = A_i - Σ⁻¹ X_i (E[X_i'Σ⁻¹X_i])⁻¹` in the textbook proof. -/
theorem sur_efficiency_vs_systemAsymptoticVariance_of_population_expansion
    (Q Omega M : Matrix k k ℝ) (B : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hB : Integrable (fun ω => systemMiddleTerm (B ω) Sigma) μ)
    (hSigma : Sigma.PosSemidef)
    (hgap :
      systemAsymptoticVariance Q Omega - surAsymptoticVariance M =
        systemPopulationMiddle μ B Sigma) :
    (systemAsymptoticVariance Q Omega - surAsymptoticVariance M).PosSemidef := by
  simpa [surAsymptoticVariance] using
    population_generalizedGaussMarkov_variance_gap_posSemidef_of_expansion
      (μ := μ) (V := systemAsymptoticVariance Q Omega) (M := M)
      (B := B) (Sigma := Sigma) hB hSigma (by simpa [surAsymptoticVariance] using hgap)

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

omit [Fintype n] [DecidableEq n] in
/-- Inverse-CMT bridge for the actual feasible SUR residual covariance
`Σ̂ = n⁻¹∑ êᵢêᵢ'`. -/
theorem surResidualCovarianceStarObs_inverse_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          surResidualCovarianceStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        surResidualCovarianceStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det) :
    TendstoInMeasure μ
      (fun t ω =>
        (surResidualCovarianceStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
      atTop (fun _ => Sigma⁻¹) :=
  tendstoInMeasure_matrix_inv hSigmaHat_meas hSigmaHat (fun _ => hSigma_unit)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Measurability of the inverse feasible SUR residual covariance. -/
theorem surResidualCovarianceStarObs_inverse_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          surResidualCovarianceStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ)
    (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        (surResidualCovarianceStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹) μ :=
  aestronglyMeasurable_matrix_inv (hSigmaHat_meas t)

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

/-- Hansen Theorem 11.6 wrapper for the actual feasible SUR residual covariance.

This specializes the estimated-inverse covariance route to
`Σ̂ = surResidualCovarianceStarObs X Y`. The remaining assumption `hsub` is the
primitive perturbation statement that replacing `Σ⁻¹` by `Σ̂⁻¹` inside
`n⁻¹∑ X_i' (·) X_i` changes the information matrix by `o_p(1)`. -/
theorem surCovariance_consistent_of_residualCovarianceStarObs_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ)
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hMhat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((surResidualCovarianceStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)) μ)
    (hsub : TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((surResidualCovarianceStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹) -
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)
      atTop (fun _ => 0))
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surVarianceEstimator
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((surResidualCovarianceStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovariance_consistent_of_estimated_inverse_cov_substitution
    (μ := μ) (X := X) (SigmaInv := Sigma⁻¹)
    (SigmaInvHat := fun t ω =>
      (surResidualCovarianceStarObs
        (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
    hint hindep hident hMhat_meas hsub hM_unit

end HansenEconometrics
