import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.AsymptoticUtils.DeltaMethod
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

omit [DecidableEq q] [DecidableEq m] in
/-- System-score condition package for Hansen Theorem 11.1 at the
observation-system level.

It records the real probabilistic ingredients used by the proof route:
convergence of `Q̂ = n⁻¹∑ Xᵢ'Xᵢ`, a vector CLT for
`√n n⁻¹∑ Xᵢ'eᵢ`, nonsingularity and symmetry of the population Gram inverse,
and positive semidefiniteness of the score covariance. -/
structure SystemScoreCLTConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Q Omega : Matrix k k ℝ) : Prop where
  gram_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ
  gram_tendsto : TendstoInMeasure μ
    (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
    atTop (fun _ => Q)
  gram_nonsing : IsUnit Q.det
  gram_inv_transpose : (Q⁻¹)ᵀ = Q⁻¹
  score_limit : TendstoInDistribution
    (fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω))
    atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
    (multivariateGaussian 0 Omega)
  score_cov_posSemidef : Omega.PosSemidef

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The Hansen coefficient covariance `Q⁻¹ΩQ⁻¹` is positive semidefinite when
`Ω` is positive semidefinite and `Q⁻¹` is symmetric. -/
theorem systemAsymptoticVariance_posSemidef
    {Q Omega : Matrix k k ℝ}
    (hOmega : Omega.PosSemidef) (hQsymm : (Q⁻¹)ᵀ = Q⁻¹) :
    (systemAsymptoticVariance Q Omega).PosSemidef := by
  have hpsd : (Q⁻¹ * Omega * (Q⁻¹)ᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose] using
      Matrix.PosSemidef.mul_mul_conjTranspose_same hOmega Q⁻¹
  simpa [systemAsymptoticVariance, hQsymm] using hpsd

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Linearized Hansen Theorem 11.1 at the observation-system level.

If `Q̂ →p Q` and the system score mean obeys the vector CLT with covariance
`Ω`, then the feasible linearized statistic `Q̂⁻¹√n ĝ` has the Gaussian limit
with covariance `Q⁻¹ΩQ⁻¹`. -/
theorem systemLinearizedScore_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
          (Real.sqrt (t : ℝ) •
            systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) := by
  have hQinv : TendstoInMeasure μ
      (fun (t : ℕ) ω => (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹)
      atTop (fun _ => Q⁻¹) :=
    tendstoInMeasure_matrix_inv h.gram_meas h.gram_tendsto (fun _ => h.gram_nonsing)
  have hQinv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => (systemNormalizedGram (fun i : Fin n => X i.val ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.gram_meas n)
  have hlin :=
    randomMatrix_mulVec_tendstoInDistribution_multivariateGaussian
      (Ahat := fun (t : ℕ) ω => (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹)
      (A := Q⁻¹) (S := Omega)
      (T := fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω))
      h.score_cov_posSemidef hQinv_meas hQinv h.score_limit
  simpa [systemAsymptoticVariance, h.gram_inv_transpose] using hlin

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The sample system Gram is singular with asymptotically vanishing probability
whenever `Q̂ →ₚ Q` and the population Gram is nonsingular. -/
theorem measure_systemNormalizedGram_singular_tendsto_zero
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) :
    Tendsto
      (fun n => μ {ω |
        ¬ IsUnit (systemNormalizedGram (fun i : Fin n => X i.val ω)).det})
      atTop (𝓝 0) := by
  have hDet : TendstoInMeasure μ
      (fun n ω => (systemNormalizedGram (fun i : Fin n => X i.val ω)).det)
      atTop (fun _ => Q.det) :=
    tendstoInMeasure_continuous_comp h.gram_meas h.gram_tendsto
      (Continuous.matrix_det continuous_id)
  have hqne : Q.det ≠ 0 := h.gram_nonsing.ne_zero
  set ε : ℝ := |Q.det| / 2 with hε_def
  have hε_pos : 0 < ε := half_pos (abs_pos.mpr hqne)
  have hε_le : ε ≤ |Q.det| := by
    rw [hε_def]
    linarith [abs_nonneg Q.det]
  have hmeas_eps := hDet (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas_eps
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero, not_not] at hω
  simp only [Set.mem_setOf_eq, hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
  exact ENNReal.ofReal_le_ofReal hε_le

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen-facing system least-squares CLT from a proved system linearization.

The theorem is stated for observation-level system regressors and vector
outcomes. The remaining proof obligation is exactly the finite-sample/asymptotic
linearization of the chosen totalized estimator around `Q̂⁻¹√n ĝ`; once that is
available, the Gaussian limit follows from `systemLinearizedScore_tendstoInDistribution`. -/
theorem systemLeastSquaresBetaStarObs_tendstoInDistribution_of_linearization
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hlinearization : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0))
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (t : ℕ) ω =>
      (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
        (Real.sqrt (t : ℝ) •
          systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
    (Y := fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (systemLeastSquaresBetaStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    (systemLinearizedScore_tendstoInDistribution (μ := μ) h)
    hlinearization hmeas

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Exact Chapter 11.1 Star-estimator linearization on nonsingular sample Grams.

The normalized finite-sample identity in `Systems.lean` leaves only the
totalized singular-design remainder
`(Q̂ₙ⁻¹ Q̂ₙ - I) β`. On samples where `Q̂ₙ` is nonsingular this remainder is
exactly zero, so the scaled estimator error equals the linearized score. -/
theorem systemLeastSquaresBetaStarObs_linearization_of_nonsingular
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hQhat_unit : ∀ t ω,
      IsUnit (systemNormalizedGram (fun i : Fin t => X i.val ω)).det) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
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
  let Qhat : Matrix k k ℝ := systemNormalizedGram Xt
  let ghat : k → ℝ := systemScoreMean Xt et
  let betaHat : k → ℝ := systemLeastSquaresBetaStarObs Xt Yt
  have hid :
      betaHat - β - Qhat⁻¹ *ᵥ ghat =
        ((Qhat)⁻¹ * Qhat - 1) *ᵥ β := by
    simpa [betaHat, Qhat, ghat, Xt, et, Yt] using
      systemLeastSquaresBetaStarObs_sub_identity_normalized
        (X := Xt) (e := et) (Y := Yt) (β := β)
        (by intro i j; exact hmodel i.val ω j)
  have hlin0 : betaHat - β - Qhat⁻¹ *ᵥ ghat = 0 := by
    rw [hid, Matrix.nonsing_inv_mul Qhat (by simpa [Qhat, Xt] using hQhat_unit t ω)]
    simp
  ext a
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  have hcoord := congrArg (fun v : k → ℝ => v a) hlin0
  simp only [Pi.sub_apply, Pi.zero_apply] at hcoord
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply]
  symm
  change Real.sqrt (t : ℝ) * (betaHat a - β a) -
      Real.sqrt (t : ℝ) * (Qhat⁻¹ *ᵥ ghat) a = 0
  calc
    Real.sqrt (t : ℝ) * (betaHat a - β a) -
        Real.sqrt (t : ℝ) * (Qhat⁻¹ *ᵥ ghat) a =
          Real.sqrt (t : ℝ) *
            (betaHat a - β a - (Qhat⁻¹ *ᵥ ghat) a) := by ring
    _ = 0 := by rw [hcoord, mul_zero]

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen Theorem 11.1 wrapper when sample normalized Grams are nonsingular.

This theorem composes the exact nonsingular finite-sample linearization with
the Chapter 11 system-score CLT package. It is stronger than the pure
linearization-interface theorem, while keeping the nonsingularity side
condition explicit rather than hiding it inside Assumption 7.2. -/
theorem systemLeastSquaresBetaStarObs_tendstoInDistribution_of_nonsingular
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hQhat_unit : ∀ t ω,
      IsUnit (systemNormalizedGram (fun i : Fin t => X i.val ω)).det)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) :=
  systemLeastSquaresBetaStarObs_tendstoInDistribution_of_linearization
    (μ := μ) h β
    (systemLeastSquaresBetaStarObs_linearization_of_nonsingular
      (μ := μ) (X := X) (e := e) (Y := Y) β hmodel hQhat_unit)
    hmeas

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Exact Chapter 11.1 Star-estimator linearization with the singular-design
remainder handled by a high-probability argument.

This removes the global sample-Gram nonsingularity side condition from
`systemLeastSquaresBetaStarObs_linearization_of_nonsingular`: on nonsingular
samples the residual is exactly zero, and the singular event has probability
tending to zero by `measure_systemNormalizedGram_singular_tendsto_zero`. -/
theorem systemLeastSquaresBetaStarObs_linearization
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  have hsingular := measure_systemNormalizedGram_singular_tendsto_zero h
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
  let Qhat : Matrix k k ℝ := systemNormalizedGram Xt
  let ghat : k → ℝ := systemScoreMean Xt et
  let betaHat : k → ℝ := systemLeastSquaresBetaStarObs Xt Yt
  have hid :
      betaHat - β - Qhat⁻¹ *ᵥ ghat =
        ((Qhat)⁻¹ * Qhat - 1) *ᵥ β := by
    simpa [betaHat, Qhat, ghat, Xt, et, Yt] using
      systemLeastSquaresBetaStarObs_sub_identity_normalized
        (X := Xt) (e := et) (Y := Yt) (β := β)
        (by intro i j; exact hmodel i.val ω j)
  have hlin0 : betaHat - β - Qhat⁻¹ *ᵥ ghat = 0 := by
    rw [hid, Matrix.nonsing_inv_mul Qhat (by simpa [Qhat, Xt] using hunit)]
    simp
  have hzero :
      Real.sqrt (t : ℝ) • (betaHat - β) -
        Qhat⁻¹ *ᵥ (Real.sqrt (t : ℝ) • ghat) = 0 := by
    rw [Matrix.mulVec_smul, ← smul_sub, hlin0, smul_zero]
  change ε ≤ edist
    (((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
        t ω) 0 at hω
  have hω0 : ε = 0 := by
    simpa [Xt, et, Yt, Qhat, ghat, betaHat, hzero] using hω
  exact hε.ne' hω0

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen Theorem 11.1 at the system-score interface, with sample singularity
handled by the totalized Star estimator and the high-probability Gram argument. -/
theorem systemLeastSquaresBetaStarObs_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) :=
  systemLeastSquaresBetaStarObs_tendstoInDistribution_of_linearization
    (μ := μ) h β
    (systemLeastSquaresBetaStarObs_linearization
      (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel)
    hmeas

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The Chapter 11.1 system LS CLT implies the scaled system coefficient
error is `Oₚ(1)`. This is the stochastic boundedness input for Hansen
Theorem 11.2. -/
theorem systemLeastSquaresBetaStarObs_sqrt_sub_boundedInProbabilityNorm
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    BoundedInProbabilityNorm μ
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) := by
  exact BoundedInProbabilityNorm.of_tendstoInDistribution
    (systemLeastSquaresBetaStarObs_tendstoInDistribution
      (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeas)

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Consistency of the Chapter 11 system Star estimator as a corollary of the
system LS CLT. -/
theorem systemLeastSquaresBetaStarObs_tendstoInMeasure_beta
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInMeasure μ
      (fun t ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) := by
  let βhat : ℕ → Ω → k → ℝ := fun t ω =>
    systemLeastSquaresBetaStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)
  have hbounded : BoundedInProbabilityNorm μ
      (fun (t : ℕ) ω => Real.sqrt (t : ℝ) • (βhat t ω - β)) := by
    simpa [βhat] using
      systemLeastSquaresBetaStarObs_sqrt_sub_boundedInProbabilityNorm
        (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeas
  have hinv_sqrt : Tendsto (fun t : ℕ => (Real.sqrt (t : ℝ))⁻¹)
      atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hscaled :
      TendstoInMeasure μ
        (fun (t : ℕ) (ω : Ω) => ((Real.sqrt (t : ℝ))⁻¹) •
          ((Real.sqrt (t : ℝ)) • (βhat t ω - β)))
        atTop (fun _ => (0 : k → ℝ)) :=
    hbounded.tendstoInMeasure_const_smul_zero hinv_sqrt
  have hdiff : TendstoInMeasure μ (fun t ω => βhat t ω - β)
      atTop (fun _ => (0 : k → ℝ)) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hscaled
    filter_upwards [eventually_atTop.2 ⟨1, fun t ht => ht⟩] with t ht
    exact ae_of_all μ (fun ω => by
      have htpos_nat : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht
      have htpos : 0 < (t : ℝ) := Nat.cast_pos.mpr htpos_nat
      have hsqrt_ne : Real.sqrt (t : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr htpos
      ext a
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul])
  have hconst : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => β)
      atTop (fun _ => β) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  exact TendstoInMeasure.of_sub_tendsto_zero_vector hdiff hconst

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

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype m] [DecidableEq m] in
/-- Hansen Assumption 7.3/Chapter 11.2 deterministic smoothness package for a
function of the system coefficient vector.

The derivative of `r` at `β` is represented by Hansen's matrix `R`, with
linear action `v ↦ Rᵀv`. The stochastic Taylor-remainder negligibility needed
for Theorem 11.2 is intentionally kept outside this deterministic package. -/
structure SystemDeltaAssumption73
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (R : Matrix k q ℝ) where
  /-- Fréchet derivative of `r` at `β`. -/
  derivative : (k → ℝ) →L[ℝ] (q → ℝ)
  /-- Differentiability at the true parameter. -/
  differentiable_at : HasFDerivAt r derivative β
  /-- The derivative is represented by `Rᵀ`. -/
  derivative_apply : ∀ v : k → ℝ, derivative v = Rᵀ *ᵥ v
  /-- Hansen's full-rank derivative condition. -/
  fullRank : Function.Injective R.mulVec

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype m] [DecidableEq m] in
/-- Deterministic Taylor remainder for Hansen Theorem 11.2:
`r(b) - r(β) - Rᵀ(b - β)`. -/
noncomputable def systemDeltaTaylorRemainder
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (R : Matrix k q ℝ) :
    (k → ℝ) → (q → ℝ) :=
  fun b => r b - r β - Rᵀ *ᵥ (b - β)

namespace SystemDeltaAssumption73

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q]
  [Fintype m] [DecidableEq m] in
/-- Assumption 7.3 supplies the deterministic little-o Taylor remainder. -/
theorem taylorRemainder_isLittleO
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SystemDeltaAssumption73 r β R) :
    systemDeltaTaylorRemainder r β R =o[𝓝 β] (fun b => b - β) := by
  simpa [systemDeltaTaylorRemainder, h73.derivative_apply] using
    deltaMethod_remainder_isLittleO h73.differentiable_at

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q]
  [Fintype m] [DecidableEq m] in
/-- Algebraic form of the Taylor expansion around `β`. -/
theorem taylorExpansion_eq_linear_plus_remainder
    {r : (k → ℝ) → (q → ℝ)} {β b : k → ℝ} {R : Matrix k q ℝ}
    (_h73 : SystemDeltaAssumption73 r β R) :
    r b - r β =
      Rᵀ *ᵥ (b - β) + systemDeltaTaylorRemainder r β R b := by
  ext j
  simp [systemDeltaTaylorRemainder]

end SystemDeltaAssumption73

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q] in
/-- Hansen Theorem 11.2 Taylor-remainder bridge.

If the coefficient estimator is consistent and its scaled coefficient error is
`Oₚ(1)`, Assumption 7.3's deterministic little-o Taylor remainder is negligible
after the same scaling. -/
theorem systemDelta_scaled_taylor_remainder_tendstoInMeasure_of_consistency_bounded
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SystemDeltaAssumption73 r β R)
    (root : ℕ → ℝ) (βhat : ℕ → Ω → k → ℝ)
    (hβ : TendstoInMeasure μ βhat atTop (fun _ => β))
    (hTβ : BoundedInProbabilityNorm μ
      (fun n ω => root n • (βhat n ω - β))) :
    TendstoInMeasure μ
      (fun n ω => root n • systemDeltaTaylorRemainder r β R (βhat n ω))
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
        ‖systemDeltaTaylorRemainder r β R b‖ ≤ η * ‖b - β‖ :=
    (SystemDeltaAssumption73.taylorRemainder_isLittleO h73).def hηpos
  rcases Metric.mem_nhds_iff.1 hnear with ⟨ρ, hρpos, hρsub⟩
  have hβev := (hβ ρ hρpos).eventually_lt_const hδ2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hMev.and hβev)
  refine ⟨N, fun n hnN => ?_⟩
  have hnM : μ {ω | M ≤ ‖root n • (βhat n ω - β)‖} ≤ δ / 2 := (hN n hnN).1
  have hnβ : μ {ω | ρ ≤ dist (βhat n ω) β} < δ / 2 := (hN n hnN).2
  have hnβ_le : μ {ω | ρ ≤ dist (βhat n ω) β} ≤ δ / 2 := le_of_lt hnβ
  have hcover :
      {ω | ε ≤ dist
        (root n • systemDeltaTaylorRemainder r β R (βhat n ω)) 0} ⊆
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
        ‖systemDeltaTaylorRemainder r β R (βhat n ω)‖ ≤
          η * ‖βhat n ω - β‖ :=
      hρsub hbmem
    have hscaled_bound :
        ‖root n • systemDeltaTaylorRemainder r β R (βhat n ω)‖ ≤
          η * ‖root n • (βhat n ω - β)‖ := by
      calc
        ‖root n • systemDeltaTaylorRemainder r β R (βhat n ω)‖
            = ‖root n‖ * ‖systemDeltaTaylorRemainder r β R (βhat n ω)‖ :=
              norm_smul _ _
        _ ≤ ‖root n‖ * (η * ‖βhat n ω - β‖) :=
              mul_le_mul_of_nonneg_left hrem_bound (norm_nonneg _)
        _ = η * (‖root n‖ * ‖βhat n ω - β‖) := by ring
        _ = η * ‖root n • (βhat n ω - β)‖ := by rw [norm_smul]
    have hscaled_lt : ‖root n • systemDeltaTaylorRemainder r β R (βhat n ω)‖ < ε := by
      calc
        ‖root n • systemDeltaTaylorRemainder r β R (βhat n ω)‖
            ≤ η * ‖root n • (βhat n ω - β)‖ := hscaled_bound
        _ < η * M := mul_lt_mul_of_pos_left hTsmall hηpos
        _ = ε := div_mul_cancel₀ ε hMpos.ne'
    have hdist_lt :
        dist (root n • systemDeltaTaylorRemainder r β R (βhat n ω)) 0 < ε := by
      simpa [dist_eq_norm] using hscaled_lt
    exact (not_le_of_gt hdist_lt) hω
  calc
    μ {ω | ε ≤ dist
        (root n • systemDeltaTaylorRemainder r β R (βhat n ω)) 0}
        ≤ μ ({ω | M ≤ ‖root n • (βhat n ω - β)‖} ∪
          {ω | ρ ≤ dist (βhat n ω) β}) := measure_mono hcover
    _ ≤ μ {ω | M ≤ ‖root n • (βhat n ω - β)‖} +
          μ {ω | ρ ≤ dist (βhat n ω) β} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hnM hnβ_le
    _ = δ := ENNReal.add_halves δ

/-- Stable nonlinear-delta linearization interface for Hansen Theorem 11.2.

`Tβ` is the scaled coefficient statistic and `Tθ` is the scaled statistic for a
smooth function of the coefficients. The expansion records the Assumption 7.3
Taylor remainder: `Tθ = Rᵀ Tβ + oₚ(1)`. -/
structure SystemDeltaLinearization
    (μ : Measure Ω)
    (Tθ : ℕ → Ω → q → ℝ) (R : Matrix k q ℝ) (Tβ : ℕ → Ω → k → ℝ) : Prop where
  scaled_measurable : ∀ n, AEMeasurable (Tθ n) μ
  expansion : TendstoInMeasure μ
    (Tθ - fun n ω => Rᵀ *ᵥ Tβ n ω) atTop (fun _ => 0)

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q] [Fintype m] [DecidableEq m] in
/-- Constructor for the Chapter 11 nonlinear-delta interface from the scaled Taylor
remainder associated with `SystemDeltaAssumption73`. -/
theorem systemDeltaLinearization_of_scaled_taylor_remainder
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (_h73 : SystemDeltaAssumption73 r β R)
    (root : ℕ → ℝ) (βhat : ℕ → Ω → k → ℝ)
    (hscaled_meas : ∀ n,
      AEMeasurable (fun ω => root n • (r (βhat n ω) - r β)) μ)
    (hrem : TendstoInMeasure μ
      (fun n ω => root n • systemDeltaTaylorRemainder r β R (βhat n ω))
      atTop (fun _ => 0)) :
    SystemDeltaLinearization μ
      (fun n ω => root n • (r (βhat n ω) - r β)) R
      (fun n ω => root n • (βhat n ω - β)) where
  scaled_measurable := hscaled_meas
  expansion := by
    have heq :
        ((fun n ω => root n • (r (βhat n ω) - r β)) -
            fun n ω => Rᵀ *ᵥ (root n • (βhat n ω - β))) =
          fun n ω => root n • systemDeltaTaylorRemainder r β R (βhat n ω) := by
      funext n ω
      ext j
      simp [systemDeltaTaylorRemainder, sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_neg, smul_neg, smul_eq_mul]
      ring_nf
    simpa [heq] using hrem

/-- Hansen Theorem 11.2 at the stable nonlinear-delta interface.

Once a coefficient statistic has covariance `Vβ` and the smooth target has the
linearization `RᵀTβ + oₚ(1)`, the smooth target has covariance `RᵀVβR`. -/
theorem systemDelta_tendstoInDistribution_multivariateGaussian_of_linearization
    (Tθ : ℕ → Ω → q → ℝ) (R : Matrix k q ℝ) (Tβ : ℕ → Ω → k → ℝ)
    (Vβ : Matrix k k ℝ) (hVβ : Vβ.PosSemidef)
    (hTβ : TendstoInDistribution Tβ atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 Vβ))
    (hlinear : SystemDeltaLinearization μ Tθ R Tβ) :
    TendstoInDistribution Tθ atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) := by
  let Tβe : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (Tβ n ω)
  have hTβe :
      TendstoInDistribution Tβe atTop (fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 Vβ) := by
    have hmap := hTβ.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [Tβe, Function.comp_def] using hmap
  have hlinE :
      TendstoInDistribution
        (fun n => matrixContinuousLinearMap Rᵀ ∘ Tβe n)
        atTop (matrixContinuousLinearMap Rᵀ ∘ fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 Vβ) :=
    hTβe.continuous_comp (matrixContinuousLinearMap Rᵀ).continuous
  have hLaw : HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap Rᵀ z)
      (multivariateGaussian 0 (systemDeltaVariance Vβ R)) (multivariateGaussian 0 Vβ) := by
    simpa [systemDeltaVariance, matrixContinuousLinearMap,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := q) hVβ Rᵀ
  have htargetE :
      TendstoInDistribution
        (fun n ω => matrixContinuousLinearMap Rᵀ (Tβe n ω))
        atTop (fun z : EuclideanSpace ℝ q => z)
        (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ q) hlinE hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : q => ℝ))
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => Rᵀ *ᵥ Tβ n ω) (Y := Tθ)
    (Z := fun z : EuclideanSpace ℝ q => z.ofLp)
    (by
      simpa [Tβe, Function.comp_def, matrixContinuousLinearMap_apply] using htarget)
    hlinear.expansion hlinear.scaled_measurable

/-- Hansen Theorem 11.2 from the Chapter 11 Gaussian-limit interface and a
stable nonlinear-delta linearization. -/
theorem systemDelta_tendstoInDistribution_multivariateGaussian_of_gaussianLimit
    (Tθ : ℕ → Ω → q → ℝ) (R : Matrix k q ℝ) (Tβ : ℕ → Ω → k → ℝ)
    (Vβ : Matrix k k ℝ)
    (hTβ : GaussianLimit μ Tβ Vβ)
    (hlinear : SystemDeltaLinearization μ Tθ R Tβ) :
    TendstoInDistribution Tθ atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) :=
  systemDelta_tendstoInDistribution_multivariateGaussian_of_linearization
    Tθ R Tβ Vβ hTβ.covariance_posSemidef hTβ.limit hlinear

omit [DecidableEq m] in
/-- Hansen Theorem 11.2, concrete system least-squares Delta-method wrapper.

Combines the system LS CLT from Theorem 11.1, the derived consistency and
`Oₚ(1)` scaled coefficient error, and Assumption 7.3's Taylor remainder to
obtain the Gaussian limit for `√n (r(β̂ₙ) - r(β))`. -/
theorem systemDelta_systemLeastSquaresBetaStarObs_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega)
    (h73 : SystemDeltaAssumption73 r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeasβ : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hmeasθ : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance (systemAsymptoticVariance Q Omega) R)) := by
  let βhat : ℕ → Ω → k → ℝ := fun t ω =>
    systemLeastSquaresBetaStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)
  have hβclt : TendstoInDistribution
      (fun (t : ℕ) ω => Real.sqrt (t : ℝ) • (βhat t ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) := by
    simpa [βhat] using
      systemLeastSquaresBetaStarObs_tendstoInDistribution
        (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeasβ
  have hβbounded : BoundedInProbabilityNorm μ
      (fun (t : ℕ) ω => Real.sqrt (t : ℝ) • (βhat t ω - β)) := by
    simpa [βhat] using
      systemLeastSquaresBetaStarObs_sqrt_sub_boundedInProbabilityNorm
        (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeasβ
  have hβcons : TendstoInMeasure μ βhat atTop (fun _ => β) := by
    simpa [βhat] using
      systemLeastSquaresBetaStarObs_tendstoInMeasure_beta
        (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeasβ
  have hrem : TendstoInMeasure μ
      (fun (t : ℕ) (ω : Ω) => Real.sqrt (t : ℝ) •
        systemDeltaTaylorRemainder r β R (βhat t ω))
      atTop (fun _ => (0 : q → ℝ)) :=
    systemDelta_scaled_taylor_remainder_tendstoInMeasure_of_consistency_bounded
      (μ := μ) h73 (fun t : ℕ => Real.sqrt (t : ℝ)) βhat hβcons hβbounded
  have hlinear : SystemDeltaLinearization μ
      (fun t ω => Real.sqrt (t : ℝ) • (r (βhat t ω) - r β)) R
      (fun t ω => Real.sqrt (t : ℝ) • (βhat t ω - β)) :=
    systemDeltaLinearization_of_scaled_taylor_remainder
      (μ := μ) h73 (fun t : ℕ => Real.sqrt (t : ℝ)) βhat
      (by simpa [βhat] using hmeasθ) hrem
  have hV : (systemAsymptoticVariance Q Omega).PosSemidef :=
    systemAsymptoticVariance_posSemidef h.score_cov_posSemidef h.gram_inv_transpose
  exact systemDelta_tendstoInDistribution_multivariateGaussian_of_linearization
    (μ := μ)
    (Tθ := fun t ω => Real.sqrt (t : ℝ) • (r (βhat t ω) - r β))
    (R := R)
    (Tβ := fun t ω => Real.sqrt (t : ℝ) • (βhat t ω - β))
    (Vβ := systemAsymptoticVariance Q Omega)
    hV hβclt hlinear

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
