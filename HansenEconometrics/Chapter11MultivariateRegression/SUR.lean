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
/-- Hansen SUR estimator surface with the covariance matrix written directly:
`W = Σ⁻¹`. -/
noncomputable def surBetaFromErrorCovStar
    (X : n → Matrix m k ℝ) (Sigma : Matrix m m ℝ) (Y : n → m → ℝ) : k → ℝ :=
  surBetaFromInverseCovStar X Sigma⁻¹ Y

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

omit [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Empirical scalar cross score multiplying the `(a,b)` entry of a SUR weight
matrix inside the weighted score coordinate `j`. -/
noncomputable def surWeightedScoreScalarWeight
    (X : n → Matrix m k ℝ) (e : n → m → ℝ) (a b : m) (j : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, X i a j * e i b

omit [Fintype k] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Coordinate expansion of the weighted SUR score as covariance-weight
entries times empirical scalar cross scores. -/
theorem surWeightedScoreMean_apply_eq_sum_weight
    (X : n → Matrix m k ℝ) (W : Matrix m m ℝ) (e : n → m → ℝ) (j : k) :
    surWeightedScoreMean X W e j =
      ∑ a : m, ∑ b : m,
        W a b * surWeightedScoreScalarWeight X e a b j := by
  unfold surWeightedScoreMean surWeightedScoreScalarWeight
  simp only [Pi.smul_apply, Finset.sum_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, smul_eq_mul]
  calc
    (Fintype.card n : ℝ)⁻¹ *
        (∑ i : n, ∑ a : m, X i a j * ∑ b : m, W a b * e i b)
        =
        (Fintype.card n : ℝ)⁻¹ *
          (∑ i : n, ∑ a : m, ∑ b : m,
            X i a j * W a b * e i b) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          simp [mul_assoc]
    _ = ∑ i : n, ∑ a : m, ∑ b : m,
          W a b * ((Fintype.card n : ℝ)⁻¹ * (X i a j * e i b)) := by
          simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ a : m, ∑ b : m, ∑ i : n,
          W a b * ((Fintype.card n : ℝ)⁻¹ * (X i a j * e i b)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.sum_comm]
    _ = ∑ a : m, ∑ b : m,
          W a b * ((Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i a j * e i b) := by
          simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

omit [Fintype k] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Coordinate expansion for replacing one SUR score weight matrix by another. -/
theorem surWeightedScoreMean_sub_apply_eq_sum_weight
    (X : n → Matrix m k ℝ) (W V : Matrix m m ℝ) (e : n → m → ℝ) (j : k) :
    (surWeightedScoreMean X W e - surWeightedScoreMean X V e) j =
      ∑ a : m, ∑ b : m,
        (W a b - V a b) * surWeightedScoreScalarWeight X e a b j := by
  rw [Pi.sub_apply,
    surWeightedScoreMean_apply_eq_sum_weight X W e j,
    surWeightedScoreMean_apply_eq_sum_weight X V e j]
  simp [Finset.sum_sub_distrib, sub_mul]

omit [Fintype k] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Scaled coordinate expansion for replacing one SUR score weight matrix by
another. This is the finite-sample algebra used by the feasible-weight
`oₚ(1)` score-substitution route. -/
theorem surWeightedScoreMean_scaled_sub_apply_eq_sum_weight
    (root : ℝ) (X : n → Matrix m k ℝ) (W V : Matrix m m ℝ)
    (e : n → m → ℝ) (j : k) :
    (root • surWeightedScoreMean X W e -
        root • surWeightedScoreMean X V e) j =
      ∑ a : m, ∑ b : m,
        (W a b - V a b) * (root * surWeightedScoreScalarWeight X e a b j) := by
  calc
    (root • surWeightedScoreMean X W e -
        root • surWeightedScoreMean X V e) j =
        root * (surWeightedScoreMean X W e - surWeightedScoreMean X V e) j := by
          simp [Pi.sub_apply]
          ring
    _ = root *
        (∑ a : m, ∑ b : m,
          (W a b - V a b) * surWeightedScoreScalarWeight X e a b j) := by
          rw [surWeightedScoreMean_sub_apply_eq_sum_weight]
    _ = ∑ a : m, ∑ b : m,
        (W a b - V a b) * (root * surWeightedScoreScalarWeight X e a b j) := by
          simp [Finset.mul_sum, mul_left_comm]

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype k]
  [DecidableEq k] [Fintype m] [DecidableEq m] in
/-- Scalar version of the Hansen scaling identity for SUR score weights.

When the population scalar cross score has mean zero, the scaled empirical
weight `√n n⁻¹∑ X_iaj e_ib` is exactly the centered iid scalar-CLT statistic. -/
theorem surWeightedScoreScalarWeight_sqrt_eq_inv_sqrt_sum
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (a b : m) (j : k)
    (hzero : μ[fun ω => X 0 ω a j * e 0 ω b] = 0)
    (n : ℕ) (ω : Ω) :
    Real.sqrt (n : ℝ) *
        surWeightedScoreScalarWeight
          (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b j =
      (Real.sqrt (n : ℝ))⁻¹ *
        (∑ i ∈ Finset.range n, X i ω a j * e i ω b -
          (n : ℝ) * μ[fun ω => X 0 ω a j * e 0 ω b]) := by
  have hsum :
      (∑ i : Fin n, X i.val ω a j * e i.val ω b) =
        ∑ i ∈ Finset.range n, X i ω a j * e i ω b :=
    Fin.sum_univ_eq_sum_range (fun i => X i ω a j * e i ω b) n
  rw [hzero, mul_zero, sub_zero]
  unfold surWeightedScoreScalarWeight
  simp only [Fintype.card_fin, smul_eq_mul]
  rw [hsum]
  have hscale : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
      (Real.sqrt (n : ℝ))⁻¹ := by
    simpa [div_eq_mul_inv] using (Real.sqrt_div_self (x := (n : ℝ)))
  calc
    Real.sqrt (n : ℝ) *
        ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω a j * e i ω b) =
        (Real.sqrt (n : ℝ) * (n : ℝ)⁻¹) *
          ∑ i ∈ Finset.range n, X i ω a j * e i ω b := by ring
    _ = (Real.sqrt (n : ℝ))⁻¹ *
          ∑ i ∈ Finset.range n, X i ω a j * e i ω b := by rw [hscale]

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype m] [DecidableEq m] in
/-- Boundedness in probability of a scaled scalar SUR score weight from the
one-dimensional iid CLT.

This discharges the stochastic-order input needed by the feasible-weight score
substitution whenever the primitive scalar cross products `X_iaj e_ib` are iid,
mean zero, and have a finite second moment. -/
theorem surWeightedScoreScalarWeight_boundedInProbability_of_iid_clt
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (a b : m) (j : k)
    (hmem : MemLp (fun ω => X 0 ω a j * e 0 ω b) 2 μ)
    (hindep : iIndepFun (fun i ω => X i ω a j * e i ω b) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => X i ω a j * e i ω b)
        (fun ω => X 0 ω a j * e 0 ω b) μ μ)
    (hmean : μ[fun ω => X 0 ω a j * e 0 ω b] = 0) :
    BoundedInProbability μ
      (fun t ω =>
        Real.sqrt (t : ℝ) *
          surWeightedScoreScalarWeight
            (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j) := by
  let Y : ℕ → Ω → ℝ := fun i ω => X i ω a j * e i ω b
  let σ2 : NNReal := (Var[Y 0; μ]).toNNReal
  have hZ : HasLaw (fun x : ℝ => x) (gaussianReal 0 σ2) (gaussianReal 0 σ2) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 σ2))
  have hraw := iidScalarCLT_tendstoInDistribution_gaussian
    (μ := μ) (ν := gaussianReal 0 σ2) (Y := Y) (Z := fun x : ℝ => x)
    hZ (by simpa [Y] using hmem) (by simpa [Y] using hindep)
    (fun i => by simpa [Y] using hident i)
  have htarget : TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) *
          surWeightedScoreScalarWeight
            (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j)
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 σ2) := by
    refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hraw
    intro t
    exact ae_of_all μ (fun ω => by
      simpa [Y] using
        (surWeightedScoreScalarWeight_sqrt_eq_inv_sqrt_sum
          (μ := μ) (X := X) (e := e) a b j hmean t ω).symm)
  exact BoundedInProbability.of_tendstoInDistribution htarget

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
/-- SUR estimator error identity with the weight written as the error-covariance
inverse `Σ⁻¹`. This is the Hansen-facing notation bridge for
`surBetaFromInverseCovStar_sub_identity`. -/
theorem surBetaFromErrorCovStar_sub_identity
    (X : n → Matrix m k ℝ) (Sigma : Matrix m m ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) :
    surBetaFromErrorCovStar X Sigma Y - β -
        (systemHomoskedasticMiddle X Sigma⁻¹)⁻¹ *ᵥ
          surWeightedScoreMean X Sigma⁻¹ e =
      ((systemHomoskedasticMiddle X Sigma⁻¹)⁻¹ *
          systemHomoskedasticMiddle X Sigma⁻¹ - 1) *ᵥ β := by
  simpa [surBetaFromErrorCovStar] using
    surBetaFromInverseCovStar_sub_identity
      (X := X) (W := Sigma⁻¹) (e := e) (Y := Y) (β := β) hmodel

omit [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Hansen feasible SUR covariance estimator using the residual covariance
`Σ̂ = n⁻¹∑ êᵢêᵢ'`: `(n⁻¹∑ Xᵢ'Σ̂⁻¹Xᵢ)⁻¹`. -/
noncomputable def surCovarianceEstimatorStarObs
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) : Matrix k k ℝ :=
  surVarianceEstimator
    (systemHomoskedasticMiddle X (systemSigmaHatStarObs X Y)⁻¹)

omit [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Hansen feasible SUR estimator using the residual covariance
`Σ̂ = n⁻¹∑ êᵢêᵢ'`: `(n⁻¹∑ Xᵢ'Σ̂⁻¹Xᵢ)⁻¹(n⁻¹∑ Xᵢ'Σ̂⁻¹Yᵢ)`. -/
noncomputable def surBetaEstimatorStarObs
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) : k → ℝ :=
  surBetaFromInverseCovStar X (systemSigmaHatStarObs X Y)⁻¹ Y

omit [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Textbook-facing feasible SUR estimator, explicitly totalized to zero when
the estimated SUR information matrix is singular. -/
noncomputable def surBetaEstimatorOrZeroObs
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) : k → ℝ := by
  classical
  exact
    if IsUnit
        (systemHomoskedasticMiddle X (systemSigmaHatStarObs X Y)⁻¹).det then
      surBetaEstimatorStarObs X Y
    else
      0

omit [DecidableEq n] in
@[simp]
private theorem surBetaEstimatorOrZeroObs_eq_star
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) :
    surBetaEstimatorOrZeroObs X Y = surBetaEstimatorStarObs X Y := by
  classical
  unfold surBetaEstimatorOrZeroObs
  split_ifs with h
  · rfl
  · simp [surBetaEstimatorStarObs, surBetaFromInverseCovStar,
      Matrix.nonsing_inv_apply_not_isUnit _ h]

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

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
private theorem matrix_singular_measure_tendsto_zero_of_tendstoInMeasure
    {Ahat : ℕ → Ω → Matrix k k ℝ} {A : Matrix k k ℝ}
    (hA_meas : ∀ t, AEStronglyMeasurable (Ahat t) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A))
    (hA_unit : IsUnit A.det) :
    Tendsto (fun t => μ {ω | ¬ IsUnit (Ahat t ω).det}) atTop (𝓝 0) := by
  have hDet : TendstoInMeasure μ (fun t ω => (Ahat t ω).det)
      atTop (fun _ => A.det) :=
    tendstoInMeasure_continuous_comp hA_meas hA (Continuous.matrix_det continuous_id)
  have hqne : A.det ≠ 0 := hA_unit.ne_zero
  set ε : ℝ := |A.det| / 2 with hε_def
  have hε_pos : 0 < ε := half_pos (abs_pos.mpr hqne)
  have hε_le : ε ≤ |A.det| := by
    rw [hε_def]
    linarith [abs_nonneg A.det]
  have hmeas_eps := hDet (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas_eps
    (fun _ => zero_le _) (fun t => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero, not_not] at hω
  simp only [Set.mem_setOf_eq, hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
  exact ENNReal.ofReal_le_ofReal hε_le

omit [DecidableEq n] [DecidableEq m] in
private theorem surBetaFromInverseCovStar_linearization_core
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {SigmaInvHat : ℕ → Ω → Matrix m m ℝ} {M : Matrix k k ℝ}
    (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hMhat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω)) μ)
    (hMhat_tendsto : TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          (SigmaInvHat t ω))
      atTop (fun _ => M))
    (hM_unit : IsUnit M.det) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
              (SigmaInvHat t ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω)
                (SigmaInvHat t ω) (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  have hsingular :
      Tendsto
        (fun t => μ {ω |
          ¬ IsUnit
            (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
              (SigmaInvHat t ω)).det})
        atTop (𝓝 0) :=
    matrix_singular_measure_tendsto_zero_of_tendstoInMeasure
      (μ := μ)
      (Ahat := fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          (SigmaInvHat t ω))
      (A := M) hMhat_meas hMhat_tendsto hM_unit
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
  let Wt : Matrix m m ℝ := SigmaInvHat t ω
  let Mhat : Matrix k k ℝ := systemHomoskedasticMiddle Xt Wt
  let ghat : k → ℝ := surWeightedScoreMean Xt Wt et
  let betaHat : k → ℝ := surBetaFromInverseCovStar Xt Wt Yt
  have hid :
      betaHat - β - Mhat⁻¹ *ᵥ ghat =
        (Mhat⁻¹ * Mhat - 1) *ᵥ β := by
    simpa [betaHat, Mhat, ghat, Xt, et, Yt, Wt] using
      surBetaFromInverseCovStar_sub_identity
        (X := Xt) (W := Wt) (e := et) (Y := Yt) (β := β)
        (by intro i j; exact hmodel i.val ω j)
  have hlin0 : betaHat - β - Mhat⁻¹ *ᵥ ghat = 0 := by
    rw [hid, Matrix.nonsing_inv_mul Mhat (by simpa [Mhat, Xt, Wt] using hunit)]
    simp
  have hzero :
      Real.sqrt (t : ℝ) • (betaHat - β) -
        Mhat⁻¹ *ᵥ (Real.sqrt (t : ℝ) • ghat) = 0 := by
    rw [Matrix.mulVec_smul, ← smul_sub, hlin0, smul_zero]
  change ε ≤ edist
    (((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
              (SigmaInvHat t ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω)
                (SigmaInvHat t ω) (fun i : Fin t => e i.val ω)))
        t ω) 0 at hω
  have hω0 : ε = 0 := by
    simpa [Xt, et, Yt, Wt, Mhat, ghat, betaHat, hzero] using hω
  exact hε.ne' hω0

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
private theorem measure_surInformation_singular_tendsto_zero
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {W : Matrix m m ℝ} {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X W e M) :
    Tendsto
      (fun n => μ {ω |
        ¬ IsUnit (systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) W).det})
      atTop (𝓝 0) := by
  exact matrix_singular_measure_tendsto_zero_of_tendstoInMeasure
    h.information_meas h.information_tendsto h.information_nonsing

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
  simpa using
    surBetaFromInverseCovStar_linearization_core
      (μ := μ) (X := X) (e := e) (Y := Y)
      (SigmaInvHat := fun _ _ => W) (M := M) β hmodel
      h.information_meas h.information_tendsto h.information_nonsing

/-- Hansen-facing fixed-error-covariance SUR Star-estimator linearization,
with the weight written as `Σ⁻¹`. -/
theorem surBetaFromErrorCovStar_linearization
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromErrorCovStar
            (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  simpa [surBetaFromErrorCovStar] using
    surBetaFromInverseCovStar_linearization
      (μ := μ) (X := X) (e := e) (Y := Y)
      (W := Sigma⁻¹) (M := M) h β hmodel

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

/-- Hansen Theorem 11.4 fixed-error-covariance wrapper with the SUR weight
written as `Σ⁻¹`. The stochastic content is delegated to the fixed-weight
score package specialized at that inverse covariance. -/
theorem surBetaFromErrorCovStar_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromErrorCovStar
            (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromErrorCovStar
            (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (surAsymptoticVariance M)) := by
  simpa [surBetaFromErrorCovStar] using
    surBetaFromInverseCovStar_tendstoInDistribution
      (μ := μ) (X := X) (e := e) (Y := Y)
      (W := Sigma⁻¹) (M := M) h β hmodel hmeas

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Deterministic GLS variance-gap bridge behind Hansen Theorem 11.5.

This specializes the Chapter 4 generalized Gauss-Markov variance-gap theorem to
the SUR/GLS covariance notation `(Xᵀ Ω⁻¹ X)⁻¹`. -/
theorem SUREfficiency.fromGLSVarianceGap
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
private theorem sur_efficiency_vs_olsConditionalVarianceMatrix
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
  have hgap := SUREfficiency.fromGLSVarianceGap
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
/-- Population cross middle `E[A_i'X_i]` for a system linear estimator. -/
noncomputable def systemPopulationCrossMiddle
    (μ : Measure Ω) (A X : Ω → Matrix m k ℝ) : Matrix k k ℝ :=
  ∫ ω, (A ω)ᵀ * X ω ∂μ

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem systemMiddleTerm_quadratic_eq
    (X : Matrix m k ℝ) (Sigma : Matrix m m ℝ) (a : k → ℝ) :
    a ⬝ᵥ (systemMiddleTerm X Sigma *ᵥ a) =
      (X *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X *ᵥ a)) := by
  calc
    a ⬝ᵥ (systemMiddleTerm X Sigma *ᵥ a) =
        a ⬝ᵥ ((Xᵀ * Sigma) *ᵥ (X *ᵥ a)) := by
          rw [systemMiddleTerm, Matrix.mulVec_mulVec]
    _ = a ᵥ* (Xᵀ * Sigma) ⬝ᵥ (X *ᵥ a) := by
          rw [Matrix.dotProduct_mulVec]
    _ = (X *ᵥ a) ᵥ* Sigma ⬝ᵥ (X *ᵥ a) := by
          rw [← Matrix.vecMul_mulVec]
    _ = (X *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X *ᵥ a)) := by
          rw [← Matrix.dotProduct_mulVec]

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
          refine integral_congr_ae (ae_of_all μ fun ω => ?_)
          simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using
            systemMiddleTerm_quadratic_eq (X ω) Sigma a

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Integrability of population-middle quadratic forms.

This is proof infrastructure for the strict positive-definiteness bridge below:
it lets us use `integral_eq_zero_iff_of_nonneg_ae` on
`(Xᵢa)'Σ(Xᵢa)` while keeping the public API matrix-valued. -/
private theorem systemMiddle_quadratic_integrable
    (X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma) μ)
    (a : k → ℝ) :
    Integrable (fun ω => (X ω *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X ω *ᵥ a))) μ := by
  have hsum : Integrable
      (fun ω => ∑ i, ∑ j,
        a i * ((systemMiddleTerm (X ω) Sigma) i j * a j)) μ := by
    refine integrable_finset_sum _ fun i _ => ?_
    refine integrable_finset_sum _ fun j _ => ?_
    simpa [mul_assoc] using
      ((Integrable.eval (Integrable.eval hX i) j).const_mul (a i)).mul_const (a j)
  have hpoint :
      (fun ω => ∑ i, ∑ j,
        a i * ((systemMiddleTerm (X ω) Sigma) i j * a j)) =
      fun ω => (X ω *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X ω *ᵥ a)) := by
    funext ω
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using
      systemMiddleTerm_quadratic_eq (X ω) Sigma a
  simpa [hpoint] using hsum

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

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- A positive-definite weight preserves population information
nonsingularity.

If `E[Xᵢ'Xᵢ]` is nonsingular and the fixed weight `Σ` is positive definite,
then `E[Xᵢ'ΣXᵢ]` is positive definite.  This is the linear-algebra/probability
bridge used to discharge Hansen's SUR information nonsingularity from the
Assumption 7.2 population Gram condition. -/
theorem systemPopulationMiddle_posDef_of_gram_nonsing_posDef_weight
    (X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X ω)ᵀ * X ω) μ)
    (hMiddle : Integrable (fun ω => systemMiddleTerm (X ω) Sigma) μ)
    (hGram_unit : IsUnit (∫ ω, (X ω)ᵀ * X ω ∂μ).det)
    (hSigma : Sigma.PosDef) :
    (systemPopulationMiddle μ X Sigma).PosDef := by
  classical
  have hMiddle_psd :
      (systemPopulationMiddle μ X Sigma).PosSemidef :=
    systemPopulationMiddle_posSemidef X Sigma hMiddle hSigma.posSemidef
  have hGramMiddle : Integrable
      (fun ω => systemMiddleTerm (X ω) (1 : Matrix m m ℝ)) μ := by
    simpa [systemMiddleTerm] using hGram
  have hGram_psd :
      (systemPopulationMiddle μ X (1 : Matrix m m ℝ)).PosSemidef :=
    systemPopulationMiddle_posSemidef X (1 : Matrix m m ℝ)
      hGramMiddle Matrix.PosSemidef.one
  have hGram_unit_middle :
      IsUnit (systemPopulationMiddle μ X (1 : Matrix m m ℝ)).det := by
    simpa [systemPopulationMiddle, systemMiddleTerm] using hGram_unit
  have hGram_pos :
      (systemPopulationMiddle μ X (1 : Matrix m m ℝ)).PosDef :=
    (Matrix.PosSemidef.posDef_iff_isUnit hGram_psd).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr hGram_unit_middle)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hMiddle_psd.1 ?_
  intro a ha
  have hpos_real : 0 < a ⬝ᵥ (systemPopulationMiddle μ X Sigma *ᵥ a) := by
    by_contra hnot
    have hnonneg : 0 ≤ a ⬝ᵥ (systemPopulationMiddle μ X Sigma *ᵥ a) := by
      simpa using Matrix.PosSemidef.dotProduct_mulVec_nonneg hMiddle_psd a
    have hzero : a ⬝ᵥ (systemPopulationMiddle μ X Sigma *ᵥ a) = 0 :=
      le_antisymm (le_of_not_gt hnot) hnonneg
    let f : Ω → ℝ := fun ω => (X ω *ᵥ a) ⬝ᵥ (Sigma *ᵥ (X ω *ᵥ a))
    have hf_int : Integrable f μ :=
      systemMiddle_quadratic_integrable X Sigma hMiddle a
    have hf_nonneg : 0 ≤ᵐ[μ] f :=
      ae_of_all μ fun ω => by
        simpa [f] using
          Matrix.PosSemidef.dotProduct_mulVec_nonneg hSigma.posSemidef (X ω *ᵥ a)
    have hf_integral_zero : ∫ ω, f ω ∂μ = 0 := by
      have hquad := systemPopulationMiddle_quadratic_eq_integral X Sigma hMiddle a
      simpa [f, hzero] using hquad.symm
    have hf_ae_zero : f =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hf_nonneg hf_int).1 hf_integral_zero
    have hXa_ae_zero : (fun ω => X ω *ᵥ a) =ᵐ[μ] 0 := by
      filter_upwards [hf_ae_zero] with ω hω
      by_contra hXa
      have hstrict : 0 < f ω := by
        simpa [f] using hSigma.dotProduct_mulVec_pos hXa
      exact (ne_of_gt hstrict) hω
    let g : Ω → ℝ :=
      fun ω => (X ω *ᵥ a) ⬝ᵥ ((1 : Matrix m m ℝ) *ᵥ (X ω *ᵥ a))
    have hg_integral_zero : ∫ ω, g ω ∂μ = 0 := by
      exact integral_eq_zero_of_ae (by
        filter_upwards [hXa_ae_zero] with ω hω
        simp [g, hω])
    have hg_integral_zero' :
        ∫ ω, (X ω *ᵥ a) ⬝ᵥ (X ω *ᵥ a) ∂μ = 0 := by
      simpa [g] using hg_integral_zero
    have hGram_zero :
        a ⬝ᵥ (systemPopulationMiddle μ X (1 : Matrix m m ℝ) *ᵥ a) = 0 := by
      have hquad :=
        systemPopulationMiddle_quadratic_eq_integral
          X (1 : Matrix m m ℝ) hGramMiddle a
      simpa [hg_integral_zero'] using hquad
    have hGram_strict :
        0 < a ⬝ᵥ (systemPopulationMiddle μ X (1 : Matrix m m ℝ) *ᵥ a) := by
      simpa using hGram_pos.dotProduct_mulVec_pos ha
    exact (ne_of_gt hGram_strict) hGram_zero
  simpa using hpos_real

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Hansen SUR information identity, written as a named bridge:
`M = E[Xᵢ'Σ⁻¹Xᵢ]` when the population information matrix is represented by
the Chapter 11 `systemPopulationMiddle` API. -/
theorem surInformation_eq_systemPopulationMiddle
    (X : ℕ → Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ) :
    μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹] =
      systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ := by
  rfl

omit [Fintype n] [DecidableEq n] in
/-- Hansen Assumption 7.2 plus nonsingular positive-semidefinite `Σ` imply
nonsingularity of the SUR population information
`E[Xᵢ'Σ⁻¹Xᵢ]`.

The proof reuses Assumption 7.2's nonsingularity of `E[Xᵢ'Xᵢ]` and the generic
positive-definite weighted-middle bridge above. -/
theorem surInformation_nonsing_of_systemAssumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h72 : SystemRegressionMomentConditions μ X e)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det := by
  have hSigma_unit_matrix : IsUnit Sigma :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hSigma_unit
  have hSigma_pos : Sigma.PosDef :=
    (Matrix.PosSemidef.posDef_iff_isUnit hSigma).mpr hSigma_unit_matrix
  have hGram_unit_integral :
      IsUnit (∫ ω, (X 0 ω)ᵀ * X 0 ω ∂μ).det := by
    simpa [systemPopulationGram] using h72.gram_nonsing
  have hInfo_pos :
      (systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹).PosDef :=
    systemPopulationMiddle_posDef_of_gram_nonsing_posDef_weight
      (X := fun ω => X 0 ω) (Sigma := Sigma⁻¹)
      h72.gram_integrable hSUR hGram_unit_integral hSigma_pos.inv
  have hunit :
      IsUnit (systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹).det :=
    posDef_det_isUnit _ hInfo_pos
  simpa [surInformation_eq_systemPopulationMiddle X Sigma] using hunit

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private noncomputable def matrixLeftRightContinuousLinearMap
    {ι κ ν ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ν] [Fintype ρ]
    (A : Matrix ι κ ℝ) (B : Matrix ν ρ ℝ) :
    Matrix κ ν ℝ →L[ℝ] Matrix ι ρ ℝ :=
  ({ toFun := fun M => A * M * B
     map_add' := by
       intro M N
       ext i j
       simp [Matrix.mul_apply, Finset.sum_add_distrib, add_mul, mul_add]
     map_smul' := by
       intro c M
       ext i j
       simp [Matrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm] } :
      Matrix κ ν ℝ →ₗ[ℝ] Matrix ι ρ ℝ).toContinuousLinearMap

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
@[simp] private theorem matrixLeftRightContinuousLinearMap_apply
    {ι κ ν ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ν] [Fintype ρ]
    (A : Matrix ι κ ℝ) (B : Matrix ν ρ ℝ) (M : Matrix κ ν ℝ) :
    matrixLeftRightContinuousLinearMap A B M = A * M * B :=
  rfl

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem integrable_matrix_mul_const
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    {F : Ω → Matrix ι κ ℝ} (hF : Integrable F μ)
    (C : Matrix κ ν ℝ) :
    Integrable (fun ω => F ω * C) μ := by
  classical
  let T : Matrix ι κ ℝ →L[ℝ] Matrix ι ν ℝ :=
    matrixLeftRightContinuousLinearMap (1 : Matrix ι ι ℝ) C
  simpa [T, Function.comp_def] using T.integrable_comp hF

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem integral_matrix_mul_const
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    {F : Ω → Matrix ι κ ℝ} (hF : Integrable F μ)
    (C : Matrix κ ν ℝ) :
    ∫ ω, F ω * C ∂μ = (∫ ω, F ω ∂μ) * C := by
  classical
  let T : Matrix ι κ ℝ →L[ℝ] Matrix ι ν ℝ :=
    matrixLeftRightContinuousLinearMap (1 : Matrix ι ι ℝ) C
  simpa [T, Function.comp_def] using T.integral_comp_comm hF

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem integrable_const_mul_matrix
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (C : Matrix ι κ ℝ) {F : Ω → Matrix κ ν ℝ}
    (hF : Integrable F μ) :
    Integrable (fun ω => C * F ω) μ := by
  classical
  let T : Matrix κ ν ℝ →L[ℝ] Matrix ι ν ℝ :=
    matrixLeftRightContinuousLinearMap C (1 : Matrix ν ν ℝ)
  simpa [T, Function.comp_def] using T.integrable_comp hF

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem integral_const_mul_matrix
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (C : Matrix ι κ ℝ) {F : Ω → Matrix κ ν ℝ}
    (hF : Integrable F μ) :
    ∫ ω, C * F ω ∂μ = C * ∫ ω, F ω ∂μ := by
  classical
  let T : Matrix κ ν ℝ →L[ℝ] Matrix ι ν ℝ :=
    matrixLeftRightContinuousLinearMap C (1 : Matrix ν ν ℝ)
  simpa [T, Function.comp_def] using T.integral_comp_comm hF

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem integrable_crossMiddle_swap
    {A X : Ω → Matrix m k ℝ}
    (hAX : Integrable (fun ω => (A ω)ᵀ * X ω) μ) :
    Integrable (fun ω => (X ω)ᵀ * A ω) μ := by
  refine Integrable.of_eval ?_
  intro i
  refine Integrable.of_eval ?_
  intro j
  simpa [Matrix.mul_apply, mul_comm] using
    Integrable.eval (Integrable.eval hAX j) i

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Swapping the two population cross-middle arguments transposes the result. -/
theorem systemPopulationCrossMiddle_swap
    {A X : Ω → Matrix m k ℝ}
    (hAX : Integrable (fun ω => (A ω)ᵀ * X ω) μ) :
    systemPopulationCrossMiddle μ X A =
      (systemPopulationCrossMiddle μ A X)ᵀ := by
  have hXA : Integrable (fun ω => (X ω)ᵀ * A ω) μ :=
    integrable_crossMiddle_swap (μ := μ) hAX
  ext i j
  calc
    (systemPopulationCrossMiddle μ X A) i j =
        ∫ ω, ((X ω)ᵀ * A ω) i j ∂μ := by
          exact integral_apply_apply (μ := μ)
            (f := fun ω => (X ω)ᵀ * A ω) hXA i j
    _ = ∫ ω, ((A ω)ᵀ * X ω) j i ∂μ := by
          congr with ω
          simp [Matrix.mul_apply, mul_comm]
    _ = (systemPopulationCrossMiddle μ A X) j i := by
          exact (integral_apply_apply (μ := μ)
            (f := fun ω => (A ω)ᵀ * X ω) hAX j i).symm

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem systemMiddleTerm_residualized_sur_expansion
    (A X : Matrix m k ℝ) (Sigma : Matrix m m ℝ) (M : Matrix k k ℝ)
    (hSigma_unit : IsUnit Sigma.det) (hSigma_symm : Sigmaᵀ = Sigma)
    (hM_symm : Mᵀ = M) :
    systemMiddleTerm (A - Sigma⁻¹ * X * M⁻¹) Sigma =
      systemMiddleTerm A Sigma - (Aᵀ * X) * M⁻¹ -
        M⁻¹ * (Xᵀ * A) + M⁻¹ * systemMiddleTerm X Sigma⁻¹ * M⁻¹ := by
  have hSigma_inv_symm : (Sigma⁻¹)ᵀ = Sigma⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSigma_symm]
  have hM_inv_symm : (M⁻¹)ᵀ = M⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hM_symm]
  unfold systemMiddleTerm
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    hM_inv_symm, hSigma_inv_symm]
  simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub]
  rw [Matrix.nonsing_inv_mul_cancel_left Sigma A hSigma_unit,
    Matrix.mul_nonsing_inv_cancel_left Sigma (X * M⁻¹) hSigma_unit]
  abel_nf

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem residualizedSur_integrable_components
    (A X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ) (M : Matrix k k ℝ)
    (hAX : Integrable (fun ω => (A ω)ᵀ * X ω) μ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma⁻¹) μ) :
    Integrable (fun ω => (X ω)ᵀ * A ω) μ ∧
      Integrable (fun ω => ((A ω)ᵀ * X ω) * M⁻¹) μ ∧
      Integrable (fun ω => M⁻¹ * ((X ω)ᵀ * A ω)) μ ∧
      Integrable (fun ω => M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹) μ ∧
      Integrable
        (fun ω => M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ * M⁻¹) μ := by
  have hXA : Integrable (fun ω => (X ω)ᵀ * A ω) μ :=
    integrable_crossMiddle_swap (μ := μ) hAX
  have hAXM : Integrable (fun ω => ((A ω)ᵀ * X ω) * M⁻¹) μ :=
    integrable_matrix_mul_const (μ := μ) hAX M⁻¹
  have hXAM : Integrable (fun ω => M⁻¹ * ((X ω)ᵀ * A ω)) μ :=
    integrable_const_mul_matrix (μ := μ) M⁻¹ hXA
  have hXMXLeft :
      Integrable (fun ω => M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹) μ :=
    integrable_const_mul_matrix (μ := μ) M⁻¹ hX
  have hXMX : Integrable
      (fun ω => M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ * M⁻¹) μ :=
    integrable_matrix_mul_const (μ := μ) hXMXLeft M⁻¹
  exact ⟨hXA, hAXM, hXAM, hXMXLeft, hXMX⟩

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem residualizedSur_middle_fun_eq
    (A X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ) (M : Matrix k k ℝ)
    (hSigma_unit : IsUnit Sigma.det) (hSigma_symm : Sigmaᵀ = Sigma)
    (hM_symm : Mᵀ = M) :
    (fun ω => systemMiddleTerm (A ω - Sigma⁻¹ * X ω * M⁻¹) Sigma) =
      fun ω => systemMiddleTerm (A ω) Sigma - ((A ω)ᵀ * X ω) * M⁻¹ -
        M⁻¹ * ((X ω)ᵀ * A ω) +
          M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ * M⁻¹ := by
  funext ω
  exact systemMiddleTerm_residualized_sur_expansion
    (A ω) (X ω) Sigma M hSigma_unit hSigma_symm hM_symm

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Integrability of the residualized SUR population middle follows from the
three primitive population moments in the Gauss--Markov expansion. -/
theorem systemMiddleTerm_residualized_sur_integrable
    (A X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ) (M : Matrix k k ℝ)
    (hA : Integrable (fun ω => systemMiddleTerm (A ω) Sigma) μ)
    (hAX : Integrable (fun ω => (A ω)ᵀ * X ω) μ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma⁻¹) μ)
    (hSigma_unit : IsUnit Sigma.det) (hSigma_symm : Sigmaᵀ = Sigma)
    (hM_symm : Mᵀ = M) :
    Integrable
      (fun ω => systemMiddleTerm (A ω - Sigma⁻¹ * X ω * M⁻¹) Sigma) μ := by
  rcases residualizedSur_integrable_components (μ := μ) A X Sigma M hAX hX with
    ⟨_, hAXM, hXAM, _, hXMX⟩
  rw [residualizedSur_middle_fun_eq A X Sigma M hSigma_unit hSigma_symm hM_symm]
  exact ((hA.sub hAXM).sub hXAM).add hXMX

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Population SUR Gauss--Markov gap expansion.

If `A_i` is an asymptotically linear unbiased estimator weight
(`E[A_i'X_i] = I`) and `M = E[X_i'Σ⁻¹X_i]`, then the difference between the
variance of that estimator and the SUR population variance expands as
`E[B_i'ΣB_i]`, where `B_i = A_i - Σ⁻¹X_iM⁻¹`. -/
theorem systemPopulationMiddle_sub_surAsymptoticVariance_eq_residualized_middle
    (A X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ) (M : Matrix k k ℝ)
    (hA : Integrable (fun ω => systemMiddleTerm (A ω) Sigma) μ)
    (hAX : Integrable (fun ω => (A ω)ᵀ * X ω) μ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma⁻¹) μ)
    (hSigma_unit : IsUnit Sigma.det) (hSigma_symm : Sigmaᵀ = Sigma)
    (hM_unit : IsUnit M.det) (hM_symm : Mᵀ = M)
    (hM : systemPopulationMiddle μ X Sigma⁻¹ = M)
    (hAX_one : systemPopulationCrossMiddle μ A X = 1) :
    systemPopulationMiddle μ A Sigma - surAsymptoticVariance M =
      systemPopulationMiddle μ
        (fun ω => A ω - Sigma⁻¹ * X ω * M⁻¹) Sigma := by
  rcases residualizedSur_integrable_components (μ := μ) A X Sigma M hAX hX with
    ⟨hXA, hAXM, hXAM, hXMXLeft, hXMX⟩
  have hXA_one : systemPopulationCrossMiddle μ X A = 1 := by
    rw [systemPopulationCrossMiddle_swap (μ := μ) hAX, hAX_one, Matrix.transpose_one]
  have hAXM_int : ∫ ω, ((A ω)ᵀ * X ω) * M⁻¹ ∂μ = M⁻¹ := by
    calc
      ∫ ω, ((A ω)ᵀ * X ω) * M⁻¹ ∂μ =
          systemPopulationCrossMiddle μ A X * M⁻¹ := by
            simpa [systemPopulationCrossMiddle] using
              integral_matrix_mul_const (μ := μ) hAX M⁻¹
      _ = M⁻¹ := by simp [hAX_one]
  have hXAM_int : ∫ ω, M⁻¹ * ((X ω)ᵀ * A ω) ∂μ = M⁻¹ := by
    calc
      ∫ ω, M⁻¹ * ((X ω)ᵀ * A ω) ∂μ =
          M⁻¹ * systemPopulationCrossMiddle μ X A := by
            simpa [systemPopulationCrossMiddle] using
              integral_const_mul_matrix (μ := μ) M⁻¹ hXA
      _ = M⁻¹ := by simp [hXA_one]
  have hXMX_int :
      ∫ ω, M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ * M⁻¹ ∂μ = M⁻¹ := by
    calc
      ∫ ω, M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ * M⁻¹ ∂μ =
          (M⁻¹ * systemPopulationMiddle μ X Sigma⁻¹) * M⁻¹ := by
            have hleft :
                ∫ ω, M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ ∂μ =
                  M⁻¹ * systemPopulationMiddle μ X Sigma⁻¹ := by
              simpa [systemPopulationMiddle] using
                integral_const_mul_matrix (μ := μ) M⁻¹ hX
            calc
              ∫ ω, M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ * M⁻¹ ∂μ =
                  (∫ ω, M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ ∂μ) * M⁻¹ := by
                    exact integral_matrix_mul_const (μ := μ) hXMXLeft M⁻¹
              _ = (M⁻¹ * systemPopulationMiddle μ X Sigma⁻¹) * M⁻¹ := by
                    rw [hleft]
      _ = (M⁻¹ * M) * M⁻¹ := by rw [hM]
      _ = M⁻¹ := by
            rw [Matrix.nonsing_inv_mul _ hM_unit, Matrix.one_mul]
  have hA_sub_AXM : Integrable
      (fun ω => systemMiddleTerm (A ω) Sigma - ((A ω)ᵀ * X ω) * M⁻¹) μ :=
    hA.sub hAXM
  have hA_sub_AXM_sub_XAM : Integrable
      (fun ω => systemMiddleTerm (A ω) Sigma - ((A ω)ᵀ * X ω) * M⁻¹ -
        M⁻¹ * ((X ω)ᵀ * A ω)) μ :=
    hA_sub_AXM.sub hXAM
  have hres :
      systemPopulationMiddle μ
          (fun ω => A ω - Sigma⁻¹ * X ω * M⁻¹) Sigma =
        systemPopulationMiddle μ A Sigma - surAsymptoticVariance M := by
    calc
    systemPopulationMiddle μ
        (fun ω => A ω - Sigma⁻¹ * X ω * M⁻¹) Sigma =
        ∫ ω, systemMiddleTerm (A ω) Sigma - ((A ω)ᵀ * X ω) * M⁻¹ -
          M⁻¹ * ((X ω)ᵀ * A ω) +
            M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ * M⁻¹ ∂μ := by
          rw [systemPopulationMiddle,
            residualizedSur_middle_fun_eq A X Sigma M hSigma_unit hSigma_symm hM_symm]
    _ = (∫ ω, systemMiddleTerm (A ω) Sigma ∂μ) -
          (∫ ω, ((A ω)ᵀ * X ω) * M⁻¹ ∂μ) -
          (∫ ω, M⁻¹ * ((X ω)ᵀ * A ω) ∂μ) +
          (∫ ω, M⁻¹ * systemMiddleTerm (X ω) Sigma⁻¹ * M⁻¹ ∂μ) := by
          rw [integral_add hA_sub_AXM_sub_XAM hXMX]
          rw [integral_sub hA_sub_AXM hXAM]
          rw [integral_sub hA hAXM]
    _ = systemPopulationMiddle μ A Sigma - M⁻¹ := by
          rw [hAXM_int, hXAM_int, hXMX_int]
          simp [systemPopulationMiddle]
      _ = systemPopulationMiddle μ A Sigma - surAsymptoticVariance M := by
            simp [surAsymptoticVariance]
  exact hres.symm

namespace SURScoreCLTConditions

omit [DecidableEq m] in
/-- Weighted-score iid primitive constructor for the fixed-weight SUR CLT package.

This derives the theorem-facing `SURScoreCLTConditions` fields from the
Chapter 11 WLLN for `Xᵢ'WXᵢ` and Mathlib's finite-dimensional iid CLT for the
weighted score `Xᵢ'Weᵢ`. The homoskedastic identity itself is represented by
the enforceable covariance equality `hscore_cov`. -/
theorem of_weighted_score_moments
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (W : Matrix m m ℝ)
    (hinfo_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) W) μ)
    (hinfo_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) W)))
    (hinfo_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) W)
        (fun ω => systemMiddleTerm (X 0 ω) W) μ μ)
    (hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (W *ᵥ e 0 ω)) 2 μ)
    (hscore_iIndep : iIndepFun
      (fun i ω => systemScore (X i ω) (W *ᵥ e i ω)) μ)
    (hscore_ident : ∀ i,
      IdentDistrib
        (fun ω => systemScore (X i ω) (W *ᵥ e i ω))
        (fun ω => systemScore (X 0 ω) (W *ᵥ e 0 ω)) μ μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (W *ᵥ e 0 ω)) = 0)
    (hscore_cov :
      covMat μ (fun ω => systemScore (X 0 ω) (W *ᵥ e 0 ω)) =
        μ[fun ω => systemMiddleTerm (X 0 ω) W])
    (hinfo_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) W]).det)
    (hW_posSemidef : W.PosSemidef) :
    SURScoreCLTConditions μ X W e
      (μ[fun ω => systemMiddleTerm (X 0 ω) W]) where
  information_meas :=
    fun n => systemHomoskedasticMiddle_fixed_aestronglyMeasurable
      (μ := μ) W hinfo_int hinfo_ident n
  information_tendsto :=
    systemHomoskedasticMiddle_fixed_tendstoInMeasure
      (μ := μ) W hinfo_int hinfo_indep hinfo_ident
  information_nonsing := hinfo_unit
  information_inv_transpose := by
    have hMpsd :
        (μ[fun ω => systemMiddleTerm (X 0 ω) W]).PosSemidef := by
      simpa [systemPopulationMiddle] using
        systemPopulationMiddle_posSemidef
          (μ := μ) (X := fun ω => X 0 ω) W hinfo_int hW_posSemidef
    have hM_symm :
        (μ[fun ω => systemMiddleTerm (X 0 ω) W])ᵀ =
          μ[fun ω => systemMiddleTerm (X 0 ω) W] := by
      simpa [Matrix.IsHermitian] using hMpsd.1.eq
    rw [Matrix.transpose_nonsing_inv, hM_symm]
  information_posSemidef := by
    simpa [systemPopulationMiddle] using
      systemPopulationMiddle_posSemidef
        (μ := μ) (X := fun ω => X 0 ω) W hinfo_int hW_posSemidef
  score_limit := by
    let eW : ℕ → Ω → m → ℝ := fun i ω => W *ᵥ e i ω
    let Yscore : ℕ → Ω → k → ℝ := fun i ω => systemScore (X i ω) (eW i ω)
    have hcltE :
        TendstoInDistribution
          (fun (n : ℕ) ω =>
            WithLp.toLp 2
              ((Real.sqrt (n : ℝ))⁻¹ •
                (∑ i ∈ Finset.range n, Yscore i ω -
                  (n : ℝ) • meanVec μ (Yscore 0))))
          atTop (fun z : EuclideanSpace ℝ k => z) (fun _ => μ)
          (multivariateGaussian 0 (covMat μ (Yscore 0))) :=
      iidVectorCLT_tendstoInDistribution_multivariateGaussian
        (μ := μ) (Y := Yscore) hscore_memLp hscore_iIndep hscore_ident
    have hraw :
        TendstoInDistribution
          (fun (n : ℕ) ω =>
            (Real.sqrt (n : ℝ))⁻¹ •
              (∑ i ∈ Finset.range n, Yscore i ω -
                (n : ℝ) • meanVec μ (Yscore 0)))
          atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
          (multivariateGaussian 0 (covMat μ (Yscore 0))) := by
      have hmap := hcltE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
      simpa [Yscore, Function.comp_def] using hmap
    have hscore :
        TendstoInDistribution
          (fun (n : ℕ) ω =>
            Real.sqrt (n : ℝ) •
              surWeightedScoreMean
                (fun i : Fin n => X i.val ω) W (fun i : Fin n => e i.val ω))
          atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
          (multivariateGaussian 0 (covMat μ (Yscore 0))) := by
      refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hraw
      intro n
      exact ae_of_all μ (fun ω => by
        simpa [Yscore, eW, surWeightedScoreMean, systemScoreMean, systemScore,
          Matrix.mulVec_mulVec] using
          (SystemRegressionMomentConditions.sqrt_smul_systemScoreMean_eq_inv_sqrt_sum
            (μ := μ) (X := X) (e := eW)
            (by simpa [Yscore, eW] using hscore_mean_zero) n ω).symm)
    simpa [Yscore, eW, hscore_cov] using hscore

end SURScoreCLTConditions

omit [IsProbabilityMeasure μ] [DecidableEq m] in
/-- Population Gauss-Markov variance-gap certificate.

This is the Hilbert-space analogue of the deterministic Chapter 4 variance-gap
identity used by Hansen Theorem 11.5. Once the population variance gap has been
expanded as an expected quadratic middle, positive semidefiniteness follows
from the positive semidefiniteness of the error covariance matrix. -/
private theorem population_generalizedGaussMarkov_variance_gap_posSemidef_of_expansion
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
private theorem sur_efficiency_vs_systemAsymptoticVariance_of_population_expansion
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

omit [IsProbabilityMeasure μ] in
/-- Theorem 11.5 gap equality from Hansen's primitive population identities.

This identifies the `hgap` premise of
`sur_efficiency_vs_systemAsymptoticVariance_of_population_expansion` from
`E[A_i'X_i] = I`, `M = E[X_i'Σ⁻¹X_i]`, and the variance representation
`systemAsymptoticVariance Q Ω = E[A_i'ΣA_i]`. -/
private theorem sur_population_efficiency_gap_expansion_of_moment_identities
    (Q Omega M : Matrix k k ℝ) (A X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hA : Integrable (fun ω => systemMiddleTerm (A ω) Sigma) μ)
    (hAX : Integrable (fun ω => (A ω)ᵀ * X ω) μ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma⁻¹) μ)
    (hSigma_unit : IsUnit Sigma.det) (hSigma_symm : Sigmaᵀ = Sigma)
    (hM_unit : IsUnit M.det) (hM_symm : Mᵀ = M)
    (hM : systemPopulationMiddle μ X Sigma⁻¹ = M)
    (hAX_one : systemPopulationCrossMiddle μ A X = 1)
    (hV : systemAsymptoticVariance Q Omega = systemPopulationMiddle μ A Sigma) :
    systemAsymptoticVariance Q Omega - surAsymptoticVariance M =
      systemPopulationMiddle μ
        (fun ω => A ω - Sigma⁻¹ * X ω * M⁻¹) Sigma := by
  rw [hV]
  exact systemPopulationMiddle_sub_surAsymptoticVariance_eq_residualized_middle
    (μ := μ) A X Sigma M hA hAX hX hSigma_unit hSigma_symm
    hM_unit hM_symm hM hAX_one

omit [IsProbabilityMeasure μ] in
/-- Hansen Theorem 11.5 population efficiency from primitive moment identities.

The residualized middle and the variance-gap expansion are derived internally
from `E[A_i'X_i] = I`, `M = E[X_i'Σ⁻¹X_i]`, and
`systemAsymptoticVariance Q Ω = E[A_i'ΣA_i]`, then the existing
population-expansion wrapper supplies the Loewner conclusion. -/
private theorem sur_efficiency_vs_systemAsymptoticVariance_of_moment_identities
    (Q Omega M : Matrix k k ℝ) (A X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hA : Integrable (fun ω => systemMiddleTerm (A ω) Sigma) μ)
    (hAX : Integrable (fun ω => (A ω)ᵀ * X ω) μ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM_unit : IsUnit M.det)
    (hM : systemPopulationMiddle μ X Sigma⁻¹ = M)
    (hAX_one : systemPopulationCrossMiddle μ A X = 1)
    (hV : systemAsymptoticVariance Q Omega = systemPopulationMiddle μ A Sigma) :
    (systemAsymptoticVariance Q Omega - surAsymptoticVariance M).PosSemidef := by
  have hSigma_symm : Sigmaᵀ = Sigma := by
    simpa [Matrix.IsHermitian] using hSigma.1.eq
  have hMpsd : M.PosSemidef := by
    rw [← hM]
    exact systemPopulationMiddle_posSemidef X Sigma⁻¹ hX (Matrix.PosSemidef.inv hSigma)
  have hM_symm : Mᵀ = M := by
    simpa [Matrix.IsHermitian] using hMpsd.1.eq
  let B : Ω → Matrix m k ℝ := fun ω => A ω - Sigma⁻¹ * X ω * M⁻¹
  have hB : Integrable (fun ω => systemMiddleTerm (B ω) Sigma) μ := by
    simpa [B] using
      systemMiddleTerm_residualized_sur_integrable
        (μ := μ) A X Sigma M hA hAX hX hSigma_unit hSigma_symm hM_symm
  have hgap :
      systemAsymptoticVariance Q Omega - surAsymptoticVariance M =
        systemPopulationMiddle μ B Sigma := by
    simpa [B] using
      sur_population_efficiency_gap_expansion_of_moment_identities
        (μ := μ) Q Omega M A X Sigma hA hAX hX hSigma_unit hSigma_symm
        hM_unit hM_symm hM hAX_one hV
  exact sur_efficiency_vs_systemAsymptoticVariance_of_population_expansion
    (μ := μ) Q Omega M B Sigma hB hSigma hgap

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- The population Gram integral `E[X_i'X_i]` is symmetric. -/
theorem integral_systemGram_isSymm
    (X : Ω → Matrix m k ℝ)
    (hX : Integrable (fun ω => (X ω)ᵀ * X ω) μ) :
    (∫ ω, (X ω)ᵀ * X ω ∂μ).IsSymm := by
  simpa [systemPopulationGram] using
    systemPopulationGram_isSymm (μ := μ) (X := fun _ => X) hX

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Hansen Theorem 11.5 LS-weight cross-middle identity:
`E[(X_i Q⁻¹)'X_i] = I` when `Q = E[X_i'X_i]`. -/
theorem systemPopulationCrossMiddle_olsWeight_eq_one
    (Q : Matrix k k ℝ) (X : Ω → Matrix m k ℝ)
    (hX : Integrable (fun ω => (X ω)ᵀ * X ω) μ)
    (hQ_symm : Qᵀ = Q)
    (hQ : ∫ ω, (X ω)ᵀ * X ω ∂μ = Q)
    (hQ_unit : IsUnit Q.det) :
    systemPopulationCrossMiddle μ (fun ω => X ω * Q⁻¹) X = 1 := by
  have hQinv_symm : (Q⁻¹)ᵀ = Q⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hQ_symm]
  have hpoint :
      (fun ω => (X ω * Q⁻¹)ᵀ * X ω) =
        fun ω => Q⁻¹ * ((X ω)ᵀ * X ω) := by
    funext ω
    rw [Matrix.transpose_mul, hQinv_symm]
    simp [Matrix.mul_assoc]
  calc
    systemPopulationCrossMiddle μ (fun ω => X ω * Q⁻¹) X =
        ∫ ω, Q⁻¹ * ((X ω)ᵀ * X ω) ∂μ := by
          rw [systemPopulationCrossMiddle, hpoint]
    _ = Q⁻¹ * (∫ ω, (X ω)ᵀ * X ω ∂μ) := by
          rw [integral_const_mul_matrix (μ := μ) Q⁻¹ hX]
    _ = Q⁻¹ * Q := by rw [hQ]
    _ = 1 := by rw [Matrix.nonsing_inv_mul Q hQ_unit]

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Hansen Theorem 11.5 LS-weight variance representation:
`E[(X_iQ⁻¹)'Σ(X_iQ⁻¹)] = Q⁻¹ E[X_i'ΣX_i] Q⁻¹`. -/
theorem systemPopulationMiddle_olsWeight_eq_systemAsymptoticVariance
    (Q : Matrix k k ℝ) (X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hX : Integrable (fun ω => systemMiddleTerm (X ω) Sigma) μ)
    (hQ_symm : Qᵀ = Q) :
    systemPopulationMiddle μ (fun ω => X ω * Q⁻¹) Sigma =
      systemAsymptoticVariance Q (systemPopulationMiddle μ X Sigma) := by
  have hQinv_symm : (Q⁻¹)ᵀ = Q⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hQ_symm]
  have hpoint :
      (fun ω => systemMiddleTerm (X ω * Q⁻¹) Sigma) =
        fun ω => Q⁻¹ * systemMiddleTerm (X ω) Sigma * Q⁻¹ := by
    funext ω
    unfold systemMiddleTerm
    rw [Matrix.transpose_mul, hQinv_symm]
    simp [Matrix.mul_assoc]
  have hleft : Integrable
      (fun ω => Q⁻¹ * systemMiddleTerm (X ω) Sigma) μ :=
    integrable_const_mul_matrix (μ := μ) Q⁻¹ hX
  calc
    systemPopulationMiddle μ (fun ω => X ω * Q⁻¹) Sigma =
        ∫ ω, Q⁻¹ * systemMiddleTerm (X ω) Sigma * Q⁻¹ ∂μ := by
          rw [systemPopulationMiddle, hpoint]
    _ = (∫ ω, Q⁻¹ * systemMiddleTerm (X ω) Sigma ∂μ) * Q⁻¹ := by
          rw [integral_matrix_mul_const (μ := μ) hleft Q⁻¹]
    _ = (Q⁻¹ * ∫ ω, systemMiddleTerm (X ω) Sigma ∂μ) * Q⁻¹ := by
          rw [integral_const_mul_matrix (μ := μ) Q⁻¹ hX]
    _ = systemAsymptoticVariance Q (systemPopulationMiddle μ X Sigma) := by
          simp [systemAsymptoticVariance, systemPopulationMiddle, Matrix.mul_assoc]

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 population efficiency with the least-squares influence
weight derived internally.

This wrapper specializes the general population Gauss--Markov expansion to
`A_i = X_i Q⁻¹`, derives `E[A_i'X_i] = I`, and identifies the LS asymptotic
variance as `Q⁻¹E[X_i'ΣX_i]Q⁻¹`. The remaining theorem-facing premises are the
population moment identities `Q = E[X_i'X_i]` and
`M = E[X_i'Σ⁻¹X_i]`, plus nonsingularity. -/
theorem SUREfficiency.systemLS_of_population_moments
    (Q M : Matrix k k ℝ) (X : Ω → Matrix m k ℝ) (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X ω)ᵀ * X ω) μ)
    (hLS : Integrable (fun ω => systemMiddleTerm (X ω) Sigma) μ)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hQ : ∫ ω, (X ω)ᵀ * X ω ∂μ = Q)
    (hQ_unit : IsUnit Q.det)
    (hM : systemPopulationMiddle μ X Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance Q (systemPopulationMiddle μ X Sigma) -
      surAsymptoticVariance M).PosSemidef := by
  have hQ_symm : Qᵀ = Q := by
    rw [← hQ]
    exact (integral_systemGram_isSymm (μ := μ) X hGram).eq
  let A : Ω → Matrix m k ℝ := fun ω => X ω * Q⁻¹
  have hQinv_symm : (Q⁻¹)ᵀ = Q⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hQ_symm]
  have hAeq :
      (fun ω => systemMiddleTerm (A ω) Sigma) =
        fun ω => Q⁻¹ * systemMiddleTerm (X ω) Sigma * Q⁻¹ := by
    funext ω
    unfold A systemMiddleTerm
    rw [Matrix.transpose_mul, hQinv_symm]
    simp [Matrix.mul_assoc]
  have hA : Integrable (fun ω => systemMiddleTerm (A ω) Sigma) μ := by
    rw [hAeq]
    exact integrable_matrix_mul_const
      (μ := μ) (integrable_const_mul_matrix (μ := μ) Q⁻¹ hLS) Q⁻¹
  have hAXeq :
      (fun ω => (A ω)ᵀ * X ω) =
        fun ω => Q⁻¹ * ((X ω)ᵀ * X ω) := by
    funext ω
    unfold A
    rw [Matrix.transpose_mul, hQinv_symm]
    simp [Matrix.mul_assoc]
  have hAX : Integrable (fun ω => (A ω)ᵀ * X ω) μ := by
    rw [hAXeq]
    exact integrable_const_mul_matrix (μ := μ) Q⁻¹ hGram
  have hAX_one : systemPopulationCrossMiddle μ A X = 1 := by
    simpa [A] using
      systemPopulationCrossMiddle_olsWeight_eq_one
        (μ := μ) Q X hGram hQ_symm hQ hQ_unit
  have hV :
      systemAsymptoticVariance Q (systemPopulationMiddle μ X Sigma) =
        systemPopulationMiddle μ A Sigma := by
    simpa [A] using
      (systemPopulationMiddle_olsWeight_eq_systemAsymptoticVariance
        (μ := μ) Q X Sigma hLS hQ_symm).symm
  exact sur_efficiency_vs_systemAsymptoticVariance_of_moment_identities
    (μ := μ) (Q := Q) (Omega := systemPopulationMiddle μ X Sigma) (M := M)
    (A := A) (X := X) (Sigma := Sigma)
    hA hAX hSUR hSigma hSigma_unit hM_unit hM hAX_one hV

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- The Chapter 11 population Gram API is the identity-weight population
middle. This is a notation bridge for Hansen Theorem 11.5, where the least
squares side is written with `Q = E[X_i'X_i]`. -/
private theorem systemPopulationMiddle_one_eq_systemPopulationGram
    (X : ℕ → Ω → Matrix m k ℝ) :
    systemPopulationMiddle μ (fun ω => X 0 ω) (1 : Matrix m m ℝ) =
      systemPopulationGram μ X := by
  simp [systemPopulationMiddle, systemPopulationGram, systemMiddleTerm]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m] in
/-- Weighted error second moments implied by Hansen's conditional homoskedasticity (11.8).

If the regressor products are measurable with respect to the conditioning sigma-algebra and
`E[e_a e_b | X] = Σ_ab`, then the weighted unconditional second moments can replace
`e_a e_b` by `Σ_ab`. This is the reusable scalar bridge behind the SUR score-middle identity. -/
theorem weighted_system_error_second_moment_eq_of_condExp_homoskedastic
    {mΩ : MeasurableSpace Ω} {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    (mcond : MeasurableSpace Ω) (hm : mcond ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hX_meas : ∀ a c, AEStronglyMeasurable[mcond] (fun ω => X 0 ω a c) μ)
    (hee_int : ∀ a b, Integrable (fun ω => e 0 ω a * e 0 ω b) μ)
    (hweighted_int : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b)) μ)
    (hcond : ∀ a b,
      μ[fun ω => e 0 ω a * e 0 ω b | mcond] =ᵐ[μ] fun _ => Sigma a b)
    (a b : m) (c d : k) :
    ∫ ω, X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b) ∂μ =
      ∫ ω, X 0 ω a c * X 0 ω b d * Sigma a b ∂μ := by
  let g : Ω → ℝ := fun ω => X 0 ω a c * X 0 ω b d
  let Y : Ω → ℝ := fun ω => e 0 ω a * e 0 ω b
  have hg : AEStronglyMeasurable[mcond] g μ := (hX_meas a c).mul (hX_meas b d)
  have hgY : Integrable (fun ω => g ω * Y ω) μ := by
    simpa [g, Y, mul_assoc] using hweighted_int a b c d
  have hY : Integrable Y μ := hee_int a b
  calc
    ∫ ω, X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b) ∂μ =
        ∫ ω, g ω * Y ω ∂μ := by
          simp [g, Y, mul_assoc]
    _ = ∫ ω, g ω * μ[Y | mcond] ω ∂μ := by
          exact conditioning_theorem_integral
            (m := mcond) (m₀ := mΩ) (μ := μ) hm hg hgY hY
    _ = ∫ ω, g ω * Sigma a b ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hcond a b] with ω hω
          rw [hω]
    _ = ∫ ω, X 0 ω a c * X 0 ω b d * Sigma a b ∂μ := by
          simp [g, mul_assoc]

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Hansen Theorem 11.5 score-middle identity from weighted second-moment identities.

This turns the scalar weighted identities supplied by conditional homoskedasticity into the exact
matrix equality `E[X_i'e_i e_i'X_i] = E[X_i'ΣX_i]`. -/
theorem systemPopulationScoreCovariance_eq_middle_of_weighted_error_moments
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hRobust : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hMiddle : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hWeightedError : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b)) μ)
    (hWeightedSigma : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma a b) μ)
    (hmom : ∀ a b c d,
      ∫ ω, X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b) ∂μ =
        ∫ ω, X 0 ω a c * X 0 ω b d * Sigma a b ∂μ) :
    systemPopulationScoreCovariance μ X e =
      systemPopulationMiddle μ (fun ω => X 0 ω) Sigma := by
  ext c d
  calc
    systemPopulationScoreCovariance μ X e c d =
        ∫ ω, systemRobustMiddleTerm (X 0 ω) (e 0 ω) c d ∂μ := by
          exact integral_apply_apply (μ := μ)
            (f := fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) hRobust c d
    _ = ∫ ω, ∑ b : m, ∑ a : m,
          X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          simp [systemRobustMiddleTerm, systemMiddleTerm, Matrix.mul_apply,
            Matrix.vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]
    _ = ∑ b : m, ∫ ω, ∑ a : m,
          X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b) ∂μ := by
          rw [integral_finset_sum]
          intro b _
          exact integrable_finset_sum _ fun a _ => hWeightedError a b c d
    _ = ∑ b : m, ∑ a : m,
          ∫ ω, X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b) ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [integral_finset_sum]
          intro a _
          exact hWeightedError a b c d
    _ = ∑ b : m, ∑ a : m,
          ∫ ω, X 0 ω a c * X 0 ω b d * Sigma a b ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro a _
          exact hmom a b c d
    _ = ∑ b : m, ∫ ω, ∑ a : m,
          X 0 ω a c * X 0 ω b d * Sigma a b ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [integral_finset_sum]
          intro a _
          exact hWeightedSigma a b c d
    _ = ∫ ω, ∑ b : m, ∑ a : m,
          X 0 ω a c * X 0 ω b d * Sigma a b ∂μ := by
          rw [integral_finset_sum]
          intro b _
          exact integrable_finset_sum _ fun a _ => hWeightedSigma a b c d
    _ = ∫ ω, systemMiddleTerm (X 0 ω) Sigma c d ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [] with ω
          simp [systemMiddleTerm, Matrix.mul_apply, Finset.mul_sum,
            mul_comm, mul_left_comm]
    _ = systemPopulationMiddle μ (fun ω => X 0 ω) Sigma c d := by
          exact (integral_apply_apply (μ := μ)
            (f := fun ω => systemMiddleTerm (X 0 ω) Sigma) hMiddle c d).symm

omit [DecidableEq k] [DecidableEq m] in
/-- Hansen Theorem 11.5 score-middle identity from conditional homoskedasticity (11.8).

The conclusion is the exact remaining identity
`systemPopulationScoreCovariance μ X e = systemPopulationMiddle μ (fun ω => X 0 ω) Σ`.
The assumptions expose the scalar integrability and `σ(X)`-measurability obligations needed by
the Chapter 2 conditioning theorem. -/
theorem systemPopulationScoreCovariance_eq_middle_of_condExp_homoskedastic
    {ζ : Type*} [MeasurableSpace ζ] (Z : Ω → ζ) (hZ : Measurable Z)
    [SigmaFinite (μ.trim (conditioningSpace_le hZ))]
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hRobust : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hMiddle : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hX_meas : ∀ a c,
      AEStronglyMeasurable[conditioningSpace Z] (fun ω => X 0 ω a c) μ)
    (hee_int : ∀ a b, Integrable (fun ω => e 0 ω a * e 0 ω b) μ)
    (hWeightedError : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b)) μ)
    (hWeightedSigma : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma a b) μ)
    (hcond : ∀ a b,
      condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z =ᵐ[μ] fun _ => Sigma a b) :
    systemPopulationScoreCovariance μ X e =
      systemPopulationMiddle μ (fun ω => X 0 ω) Sigma := by
  exact systemPopulationScoreCovariance_eq_middle_of_weighted_error_moments
    (μ := μ) X e Sigma hRobust hMiddle hWeightedError hWeightedSigma
    (fun a b c d =>
      weighted_system_error_second_moment_eq_of_condExp_homoskedastic
        (μ := μ) (mcond := conditioningSpace Z) (hm := conditioningSpace_le hZ)
        X e Sigma hX_meas hee_int hWeightedError
        (fun a b => by simpa [condExpOn, conditioningSpace] using hcond a b) a b c d)

omit [Fintype n] [DecidableEq n] in
/-- Enforceable scalar form of Hansen's conditional homoskedasticity condition `(11.8)`.

The package records the conditioning map, the scalar conditional second moments
`E[e_a e_b | Z] = Σ_ab`, and the integrability/measurability hypotheses needed
to turn those conditional moments into the score-middle identity in Theorem 11.5. -/
structure SystemConditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ζ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ) : Prop where
  conditioning_measurable : Measurable Z
  conditioning_sigmaFinite : SigmaFinite
    (μ.trim (conditioningSpace_le conditioning_measurable))
  robust_integrable : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ
  middle_integrable : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ
  x_conditioning_aestronglyMeasurable : ∀ a c,
    AEStronglyMeasurable[conditioningSpace Z] (fun ω => X 0 ω a c) μ
  error_second_integrable : ∀ a b, Integrable (fun ω => e 0 ω a * e 0 ω b) μ
  weighted_error_integrable : ∀ a b c d,
    Integrable (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b)) μ
  weighted_sigma_integrable : ∀ a b c d,
    Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma a b) μ
  cond_second_moment : ∀ a b,
    condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z =ᵐ[μ] fun _ => Sigma a b

/-- Literal matrix form of Hansen's SUR conditional homoskedasticity condition `(11.8)`.

The mathematical condition is `E[e_i e_i' | Z_i] = Σ`, stated as a matrix-valued conditional
expectation.  The extra fields are exactly the integrability/measurability hypotheses needed by
the existing scalar bridge `SystemConditionalHomoskedasticity`. -/
structure MatrixSystemConditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ζ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ) : Prop where
  conditioning_measurable : Measurable Z
  conditioning_sigmaFinite : SigmaFinite
    (μ.trim (conditioningSpace_le conditioning_measurable))
  robust_integrable : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ
  middle_integrable : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ
  x_conditioning_aestronglyMeasurable : ∀ a c,
    AEStronglyMeasurable[conditioningSpace Z] (fun ω => X 0 ω a c) μ
  error_outer_integrable :
    Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ
  weighted_error_integrable : ∀ a b c d,
    Integrable (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b)) μ
  weighted_sigma_integrable : ∀ a b c d,
    Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma a b) μ
  cond_error_outer :
    condExpOn μ (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) Z =ᵐ[μ] fun _ => Sigma

omit [Fintype n] [DecidableEq n] in
/-- Conditional mean-zero/exogeneity package for system errors.

The package says that the system regressors are measurable with respect to the conditioning
information and that the one-observation error vector has conditional mean zero. It is deliberately
separate from conditional homoskedasticity `(11.8)`: Hansen's second-moment condition does not by
itself imply the score mean-zero condition used in the SUR CLT. -/
structure SystemConditionalMeanZero
    {ζ : Type*} [MeasurableSpace ζ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ζ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ) : Prop where
  conditioning_measurable : Measurable Z
  conditioning_sigmaFinite : SigmaFinite
    (μ.trim (conditioningSpace_le conditioning_measurable))
  x_conditioning_aestronglyMeasurable : ∀ a c,
    AEStronglyMeasurable[conditioningSpace Z] (fun ω => X 0 ω a c) μ
  error_integrable : ∀ a, Integrable (fun ω => e 0 ω a) μ
  cond_mean_zero : ∀ a,
    condExpOn μ (fun ω => e 0 ω a) Z =ᵐ[μ] fun _ => 0

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem condExpOn_matrix_mul_left_right
    {ζ ι κ ν ρ : Type*} [MeasurableSpace ζ]
    [Fintype ι] [Fintype κ] [Fintype ν] [Fintype ρ]
    {Z : Ω → ζ} (A : Matrix ι κ ℝ) (B : Matrix ν ρ ℝ)
    {F : Ω → Matrix κ ν ℝ} {M : Matrix κ ν ℝ}
    (hF : Integrable F μ)
    (hcond : condExpOn μ F Z =ᵐ[μ] fun _ => M) :
    condExpOn μ (fun ω => A * F ω * B) Z =ᵐ[μ] fun _ => A * M * B := by
  let T : Matrix κ ν ℝ →L[ℝ] Matrix ι ρ ℝ :=
    matrixLeftRightContinuousLinearMap A B
  have hcomm :
      T ∘ condExpOn μ F Z =ᵐ[μ] condExpOn μ (T ∘ F) Z := by
    simpa [condExpOn] using
      (T.comp_condExp_comm (μ := μ) (m := conditioningSpace Z) hF)
  have hconst :
      T ∘ condExpOn μ F Z =ᵐ[μ] fun _ => A * M * B := by
    filter_upwards [hcond] with ω hω
    change A * condExpOn μ F Z ω * B = A * M * B
    exact congrArg (fun N => A * N * B) hω
  have htarget : condExpOn μ (T ∘ F) Z =ᵐ[μ] fun _ => A * M * B :=
    hcomm.symm.trans hconst
  simpa [T, Function.comp_def] using htarget

namespace SystemConditionalMeanZero

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Conditional mean-zero plus regressor measurability gives zero mean for the system score.

The scalar product integrability assumptions are the exact hypotheses needed to apply the Chapter 2
conditioning theorem to each term `X_ac e_a`. -/
theorem score_mean_zero
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemConditionalMeanZero μ Z X e)
    (hproduct : ∀ a c, Integrable (fun ω => X 0 ω a c * e 0 ω a) μ) :
    meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0 := by
  classical
  letI : SigmaFinite (μ.trim (conditioningSpace_le h.conditioning_measurable)) :=
    h.conditioning_sigmaFinite
  let S : Ω → k → ℝ := fun ω => systemScore (X 0 ω) (e 0 ω)
  have hS_int : Integrable S μ := by
    refine Integrable.of_eval ?_
    intro c
    have hrepr :
        (fun ω => S ω c) = fun ω => ∑ a : m, X 0 ω a c * e 0 ω a := by
      funext ω
      simp [S, systemScore, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [hrepr]
    exact integrable_finset_sum _ fun a _ => hproduct a c
  ext c
  have hcoord :
      meanVec μ S c = ∫ ω, S ω c ∂μ := by
    rw [meanVec]
    exact integral_apply (μ := μ) (f := S) hS_int c
  rw [hcoord]
  have hrepr :
      (fun ω => S ω c) = fun ω => ∑ a : m, X 0 ω a c * e 0 ω a := by
    funext ω
    simp [S, systemScore, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [hrepr, integral_finset_sum]
  · have hterm_zero :
        ∀ a : m, ∫ ω, X 0 ω a c * e 0 ω a ∂μ = 0 := by
      intro a
      have hcond_int :
          ∫ ω, X 0 ω a c * e 0 ω a ∂μ =
            ∫ ω, X 0 ω a c *
              condExpOn μ (fun ω => e 0 ω a) Z ω ∂μ := by
        simpa [condExpOn, conditioningSpace] using
          conditioning_theorem_integral
            (m := conditioningSpace Z) (m₀ := inferInstance) (μ := μ)
            (g := fun ω => X 0 ω a c) (Y := fun ω => e 0 ω a)
            (conditioningSpace_le h.conditioning_measurable)
            (h.x_conditioning_aestronglyMeasurable a c)
            (hproduct a c) (h.error_integrable a)
      calc
        ∫ ω, X 0 ω a c * e 0 ω a ∂μ =
            ∫ ω, X 0 ω a c *
              condExpOn μ (fun ω => e 0 ω a) Z ω ∂μ := hcond_int
        _ = ∫ _ω, 0 ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [h.cond_mean_zero a] with ω hω
            simp [hω]
        _ = 0 := by simp
    simp [hterm_zero]
  · intro a _
    exact hproduct a c

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype m] [DecidableEq m] in
/-- Conditional mean-zero errors make every integrable scalar cross product
`X_iaj e_ib` have population mean zero.

This is the scalar counterpart of `score_mean_zero`; it is useful for the
feasible-weight substitution because random SUR weights expose cross products
with arbitrary error coordinate `b`, not only the diagonal score terms. -/
theorem scalar_cross_mean_zero
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemConditionalMeanZero μ Z X e)
    (a b : m) (j : k)
    (hproduct : Integrable (fun ω => X 0 ω a j * e 0 ω b) μ) :
    μ[fun ω => X 0 ω a j * e 0 ω b] = 0 := by
  letI : SigmaFinite (μ.trim (conditioningSpace_le h.conditioning_measurable)) :=
    h.conditioning_sigmaFinite
  have hcond_int :
      ∫ ω, X 0 ω a j * e 0 ω b ∂μ =
        ∫ ω, X 0 ω a j *
          condExpOn μ (fun ω => e 0 ω b) Z ω ∂μ := by
    simpa [condExpOn, conditioningSpace] using
      conditioning_theorem_integral
        (m := conditioningSpace Z) (m₀ := inferInstance) (μ := μ)
        (g := fun ω => X 0 ω a j) (Y := fun ω => e 0 ω b)
        (conditioningSpace_le h.conditioning_measurable)
        (h.x_conditioning_aestronglyMeasurable a j)
        hproduct (h.error_integrable b)
  calc
    μ[fun ω => X 0 ω a j * e 0 ω b] =
        ∫ ω, X 0 ω a j * e 0 ω b ∂μ := rfl
    _ = ∫ ω, X 0 ω a j *
          condExpOn μ (fun ω => e 0 ω b) Z ω ∂μ := hcond_int
    _ = ∫ _ω, 0 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [h.cond_mean_zero b] with ω hω
        simp [hω]
    _ = 0 := by simp

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- The diagonal second-product integrability in the matrix conditional-homoskedasticity package
implies the first-product integrability needed by `SystemConditionalMeanZero.score_mean_zero`. -/
theorem scoreProduct_integrable_of_matrixConditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SystemConditionalMeanZero μ Z X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma) :
    ∀ a c, Integrable (fun ω => X 0 ω a c * e 0 ω a) μ := by
  intro a c
  have hmeas : AEStronglyMeasurable (fun ω => X 0 ω a c * e 0 ω a) μ :=
    ((h.x_conditioning_aestronglyMeasurable a c).mono
      (conditioningSpace_le h.conditioning_measurable)).mul
      (h.error_integrable a).aestronglyMeasurable
  have hsq : Integrable (fun ω => (X 0 ω a c * e 0 ω a) ^ 2) μ := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      hhom.weighted_error_integrable a a c c
  exact ((memLp_two_iff_integrable_sq hmeas).2 hsq).integrable (by norm_num)

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Conditional exogeneity and matrix conditional homoskedasticity imply zero mean for the system
score. -/
theorem score_mean_zero_of_matrixConditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SystemConditionalMeanZero μ Z X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma) :
    meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0 :=
  h.score_mean_zero (h.scoreProduct_integrable_of_matrixConditionalHomoskedasticity hhom)

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] [DecidableEq m] in
/-- Conditional mean zero is preserved by any fixed matrix weight, in particular by `Σ⁻¹`. -/
theorem weighted
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemConditionalMeanZero μ Z X e) (W : Matrix m m ℝ) :
    SystemConditionalMeanZero μ Z X (fun i ω => W *ᵥ e i ω) where
  conditioning_measurable := h.conditioning_measurable
  conditioning_sigmaFinite := h.conditioning_sigmaFinite
  x_conditioning_aestronglyMeasurable := h.x_conditioning_aestronglyMeasurable
  error_integrable := fun a => by
    have hrepr :
        (fun ω => (W *ᵥ e 0 ω) a) =
          fun ω => ∑ b : m, W a b * e 0 ω b := by
      funext ω
      simp [Matrix.mulVec, dotProduct]
    rw [hrepr]
    exact integrable_finset_sum _ fun b _ => (h.error_integrable b).const_mul (W a b)
  cond_mean_zero := fun a => by
    letI : SigmaFinite (μ.trim (conditioningSpace_le h.conditioning_measurable)) :=
      h.conditioning_sigmaFinite
    have hrepr :
        (fun ω => (W *ᵥ e 0 ω) a) =
          fun ω => ∑ b : m, W a b * e 0 ω b := by
      funext ω
      simp [Matrix.mulVec, dotProduct]
    have hsum_ce :
        μ[(fun ω => ∑ b : m, W a b * e 0 ω b) | conditioningSpace Z] =ᵐ[μ]
          ∑ b : m, μ[(fun ω => W a b * e 0 ω b) | conditioningSpace Z] := by
      have hsum_repr :
          (fun ω => ∑ b : m, W a b * e 0 ω b) =
            ∑ b : m, fun ω => W a b * e 0 ω b := by
        funext ω
        simp
      rw [hsum_repr]
      simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := conditioningSpace Z)
        (s := Finset.univ) (f := fun b ω => W a b * e 0 ω b)
        (fun b _ => (h.error_integrable b).const_mul (W a b))
    have hterm_zero :
        ∀ b : m, μ[(fun ω => W a b * e 0 ω b) | conditioningSpace Z] =ᵐ[μ] 0 := by
      intro b
      have hsmul :
          μ[(fun ω => W a b * e 0 ω b) | conditioningSpace Z] =ᵐ[μ]
            fun ω => W a b * μ[(fun ω => e 0 ω b) | conditioningSpace Z] ω := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (MeasureTheory.condExp_smul
            (μ := μ) (m := conditioningSpace Z) (W a b) (fun ω => e 0 ω b))
      have hzero :
          μ[(fun ω => e 0 ω b) | conditioningSpace Z] =ᵐ[μ] 0 := by
        simpa [condExpOn, conditioningSpace] using h.cond_mean_zero b
      refine hsmul.trans ?_
      filter_upwards [hzero] with ω hω
      simp [hω]
    have hsum_zero :
        (∑ b : m, μ[(fun ω => W a b * e 0 ω b) | conditioningSpace Z]) =ᵐ[μ] 0 := by
      classical
      refine Finset.induction_on (Finset.univ : Finset m) ?_ ?_
      · simp
      · intro b s hb ih
        simpa [Finset.sum_insert, hb] using (hterm_zero b).add ih
    have hfinal :
        μ[(fun ω => ∑ b : m, W a b * e 0 ω b) | conditioningSpace Z] =ᵐ[μ]
          fun _ => 0 :=
      hsum_ce.trans hsum_zero
    simpa [condExpOn, conditioningSpace, hrepr] using hfinal

end SystemConditionalMeanZero

namespace MatrixSystemConditionalHomoskedasticity

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- The matrix-valued `(11.8)` package implies the scalar package used by the existing SUR
score-middle proofs. -/
theorem toSystemConditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma) :
    SystemConditionalHomoskedasticity μ Z X e Sigma where
  conditioning_measurable := h.conditioning_measurable
  conditioning_sigmaFinite := h.conditioning_sigmaFinite
  robust_integrable := h.robust_integrable
  middle_integrable := h.middle_integrable
  x_conditioning_aestronglyMeasurable := h.x_conditioning_aestronglyMeasurable
  error_second_integrable := fun a b => by
    simpa [Matrix.vecMulVec_apply] using
      Integrable.eval (Integrable.eval h.error_outer_integrable a) b
  weighted_error_integrable := h.weighted_error_integrable
  weighted_sigma_integrable := h.weighted_sigma_integrable
  cond_second_moment := fun a b => by
    have hcoord :
        (fun ω =>
            condExpOn μ (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) Z ω a b)
          =ᵐ[μ]
        condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z := by
      simpa [condExpOn, Matrix.vecMulVec_apply] using
        condExp_apply_apply
          (m := conditioningSpace Z) (μ := μ)
          (f := fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω))
          h.error_outer_integrable a b
    have hmatrix :
        (fun ω =>
            condExpOn μ (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) Z ω a b)
          =ᵐ[μ]
        fun _ => Sigma a b := by
      filter_upwards [h.cond_error_outer] with ω hω
      exact congrFun (congrFun hω a) b
    exact hcoord.symm.trans hmatrix

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- The literal matrix `(11.8)` package identifies the unconditional error
second-moment matrix with `Σ`. -/
theorem errorOuter_integral_eq
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma) :
    μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)] = Sigma := by
  classical
  ext a b
  letI : SigmaFinite (μ.trim (conditioningSpace_le h.conditioning_measurable)) :=
    h.conditioning_sigmaFinite
  have htower :
      ∫ ω, condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z ω ∂μ =
        ∫ ω, e 0 ω a * e 0 ω b ∂μ := by
    simpa [condExpOn, conditioningSpace] using
      (MeasureTheory.integral_condExp
        (m := conditioningSpace Z) (m₀ := inferInstance) (μ := μ)
        (f := fun ω => e 0 ω a * e 0 ω b)
        (conditioningSpace_le h.conditioning_measurable))
  have hcond :
      condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z =ᵐ[μ]
        fun _ => Sigma a b :=
    h.toSystemConditionalHomoskedasticity.cond_second_moment a b
  have hcond_int :
      ∫ ω, condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z ω ∂μ =
        Sigma a b := by
    calc
      ∫ ω, condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z ω ∂μ =
          ∫ _ω, Sigma a b ∂μ := by
            exact integral_congr_ae hcond
      _ = Sigma a b := by simp
  have hentry :
      (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]) a b =
        ∫ ω, e 0 ω a * e 0 ω b ∂μ := by
    simpa [Matrix.vecMulVec_apply] using
      integral_apply_apply (μ := μ)
        (f := fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω))
        h.error_outer_integrable a b
  calc
    (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]) a b =
        ∫ ω, e 0 ω a * e 0 ω b ∂μ := hentry
    _ = ∫ ω, condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z ω ∂μ := htower.symm
    _ = Sigma a b := hcond_int

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Hansen `(11.8)` is stable under inverse-variance weighting:
if `E[e e' | Z] = Σ` and `Σ` is positive definite, then
`E[(Σ⁻¹e)(Σ⁻¹e)' | Z] = Σ⁻¹`. -/
theorem inverseWeighted_cond_error_outer
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef) :
    condExpOn μ
        (fun ω =>
          Matrix.vecMulVec (Sigma⁻¹ *ᵥ e 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) Z
      =ᵐ[μ] fun _ => Sigma⁻¹ := by
  classical
  have houter :
      (fun ω =>
          Matrix.vecMulVec (Sigma⁻¹ *ᵥ e 0 ω) (Sigma⁻¹ *ᵥ e 0 ω))
        =
      fun ω => Sigma⁻¹ * Matrix.vecMulVec (e 0 ω) (e 0 ω) * (Sigma⁻¹)ᵀ := by
    funext ω
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  have hlin :
      condExpOn μ
          (fun ω => Sigma⁻¹ * Matrix.vecMulVec (e 0 ω) (e 0 ω) * (Sigma⁻¹)ᵀ) Z
        =ᵐ[μ] fun _ => Sigma⁻¹ * Sigma * (Sigma⁻¹)ᵀ :=
    condExpOn_matrix_mul_left_right (μ := μ) (Z := Z)
      (A := Sigma⁻¹) (B := (Sigma⁻¹)ᵀ)
      h.error_outer_integrable h.cond_error_outer
  have hSigma_unit_det : IsUnit Sigma.det :=
    (Matrix.isUnit_iff_isUnit_det Sigma).mp hSigma.isUnit
  have hSigma_symm : Sigmaᵀ = Sigma := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hSigma.1.eq
  have hSigma_inv_symm : (Sigma⁻¹)ᵀ = Sigma⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSigma_symm]
  have htarget : Sigma⁻¹ * Sigma * (Sigma⁻¹)ᵀ = Sigma⁻¹ := by
    rw [hSigma_inv_symm, Matrix.nonsing_inv_mul Sigma hSigma_unit_det, Matrix.one_mul]
  exact (by simpa [houter, htarget] using hlin)

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Raw Hansen `(11.8)` implies the transformed-error matrix homoskedasticity package used by
SUR once the non-stochastic transformed weighted-product integrability side conditions are
available. The conditional second-moment field is derived by
`inverseWeighted_cond_error_outer`; it is not assumed. -/
theorem inverseWeighted
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef)
    (hrobust : Integrable
      (fun ω => systemRobustMiddleTerm (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ)
    (hmiddle : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hweighted_error : ∀ a b c d,
      Integrable
        (fun ω =>
          X 0 ω a c * X 0 ω b d *
            ((Sigma⁻¹ *ᵥ e 0 ω) a * (Sigma⁻¹ *ᵥ e 0 ω) b)) μ)
    (hweighted_sigma : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma⁻¹ a b) μ) :
    MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹ where
  conditioning_measurable := h.conditioning_measurable
  conditioning_sigmaFinite := h.conditioning_sigmaFinite
  robust_integrable := hrobust
  middle_integrable := hmiddle
  x_conditioning_aestronglyMeasurable := h.x_conditioning_aestronglyMeasurable
  error_outer_integrable := by
    let T : Matrix m m ℝ →L[ℝ] Matrix m m ℝ :=
      matrixLeftRightContinuousLinearMap Sigma⁻¹ (Sigma⁻¹)ᵀ
    have hlin : Integrable
        (fun ω => Sigma⁻¹ * Matrix.vecMulVec (e 0 ω) (e 0 ω) * (Sigma⁻¹)ᵀ) μ := by
      simpa [T, Function.comp_def] using T.integrable_comp h.error_outer_integrable
    have houter :
        (fun ω =>
            Matrix.vecMulVec (Sigma⁻¹ *ᵥ e 0 ω) (Sigma⁻¹ *ᵥ e 0 ω))
          =
        fun ω => Sigma⁻¹ * Matrix.vecMulVec (e 0 ω) (e 0 ω) * (Sigma⁻¹)ᵀ := by
      funext ω
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    simpa [houter] using hlin
  weighted_error_integrable := hweighted_error
  weighted_sigma_integrable := hweighted_sigma
  cond_error_outer := h.inverseWeighted_cond_error_outer hSigma

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- True-error residual covariance WLLN under the literal matrix `(11.8)`
target and iid outer-product hypotheses. -/
theorem trueErrorResidualCovariance_tendstoInMeasure
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))))
    (hident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ) :
    TendstoInMeasure μ
      (fun n ω => systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => Sigma) := by
  simpa [systemSigmaHat, h.errorOuter_integral_eq] using
    systemSigmaHat_ideal_tendstoInMeasure
      (μ := μ) (e := e) h.error_outer_integrable hindep hident

end MatrixSystemConditionalHomoskedasticity

namespace SystemConditionalHomoskedasticity

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- The packaged `(11.8)` scalar conditional moments imply Hansen's score-middle
identity `E[X_i'e_i e_i'X_i] = E[X_i'ΣX_i]`. -/
theorem scoreCovariance_eq_middle
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SystemConditionalHomoskedasticity μ Z X e Sigma) :
    systemPopulationScoreCovariance μ X e =
      systemPopulationMiddle μ (fun ω => X 0 ω) Sigma := by
  letI : SigmaFinite (μ.trim (conditioningSpace_le h.conditioning_measurable)) :=
    h.conditioning_sigmaFinite
  exact systemPopulationScoreCovariance_eq_middle_of_condExp_homoskedastic
    (μ := μ) Z h.conditioning_measurable X e Sigma h.robust_integrable
    h.middle_integrable h.x_conditioning_aestronglyMeasurable
    h.error_second_integrable h.weighted_error_integrable h.weighted_sigma_integrable
    h.cond_second_moment

end SystemConditionalHomoskedasticity

namespace MatrixSystemConditionalHomoskedasticity

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- The matrix-valued `(11.8)` package implies Hansen's score-middle identity. -/
theorem scoreCovariance_eq_middle
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma) :
    systemPopulationScoreCovariance μ X e =
      systemPopulationMiddle μ (fun ω => X 0 ω) Sigma :=
  h.toSystemConditionalHomoskedasticity.scoreCovariance_eq_middle

end MatrixSystemConditionalHomoskedasticity

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Hansen Theorem 11.4 weighted score-covariance identity from a packaged
conditional-homoskedasticity statement for the transformed errors `Σ⁻¹e`.

This closes the covariance-notation part of the fixed-`Σ` SUR score identity by
reusing `systemScore_covMat_eq_populationScoreCovariance` and the existing
`SystemConditionalHomoskedasticity.scoreCovariance_eq_middle` bridge. The
remaining theorem-facing content is the conditional second-moment package for
`Σ⁻¹e` itself, namely `E[(Σ⁻¹e)_a(Σ⁻¹e)_b | Z] = (Σ⁻¹)_{ab}` and its scalar
integrability/measurability fields. Deriving that package from
`E[e_a e_b | Z] = Σ_ab` would require the separate finite-sum matrix identity
`Σ⁻¹ E[ee'|Z] (Σ⁻¹)' = Σ⁻¹`. -/
private theorem weightedScore_covMat_eq_middle_of_weighted_error_conditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hscore : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hmean :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hhom : SystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹) :
    covMat μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) =
      μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹] := by
  let eW : ℕ → Ω → m → ℝ := fun i ω => Sigma⁻¹ *ᵥ e i ω
  have hcov :
      covMat μ (fun ω => systemScore (X 0 ω) (eW 0 ω)) =
        systemPopulationScoreCovariance μ X eW :=
    systemScore_covMat_eq_populationScoreCovariance
      (μ := μ) (X := X) (e := eW) hscore hmean
  have hmiddle :
      systemPopulationScoreCovariance μ X eW =
        systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ :=
    hhom.scoreCovariance_eq_middle
  simpa [eW, systemPopulationMiddle] using hcov.trans hmiddle

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Matrix-valued transformed-error conditional homoskedasticity version of
`weightedScore_covMat_eq_middle_of_weighted_error_conditionalHomoskedasticity`. -/
private theorem weightedScore_covMat_eq_middle_of_matrix_hom
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hscore : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hmean :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹) :
    covMat μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) =
      μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹] :=
  weightedScore_covMat_eq_middle_of_weighted_error_conditionalHomoskedasticity
    (μ := μ) X e Sigma hscore hmean hhom.toSystemConditionalHomoskedasticity

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5, population system-object surface.

This wrapper states the LS variance with the existing Chapter 11 population
objects `Q = E[X_i'X_i]` and `Ω = E[X_i'e_ie_i'X_i]`. The theorem-facing
primitive assumption is the homoskedastic SUR moment identity
`Ω = E[X_i'ΣX_i]`; the matrix inequality itself is delegated to the
population Gauss--Markov expansion above. -/
private theorem sur_efficiency_vs_systemLeastSquares_of_system_population_moments
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hLS : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hQ_unit : IsUnit (systemPopulationGram μ X).det)
    (hScoreCov :
      systemPopulationScoreCovariance μ X e =
        systemPopulationMiddle μ (fun ω => X 0 ω) Sigma)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef := by
  have hbase :
      (systemAsymptoticVariance (systemPopulationGram μ X)
          (systemPopulationMiddle μ (fun ω => X 0 ω) Sigma) -
        surAsymptoticVariance M).PosSemidef := by
    exact SUREfficiency.systemLS_of_population_moments
      (μ := μ) (Q := systemPopulationGram μ X) (M := M)
      (X := fun ω => X 0 ω) (Sigma := Sigma)
      hGram hLS hSUR hSigma hSigma_unit rfl hQ_unit hM hM_unit
  simpa [hScoreCov] using hbase

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 with the least-squares covariance written as
`Var(X_i'e_i)`.

The existing Chapter 11 identity `systemScore_covMat_eq_populationScoreCovariance`
turns the covariance notation into the population score-middle object, while
`hScoreCov` is the explicit homoskedastic SUR moment identity
`E[X_i'e_ie_i'X_i] = E[X_i'ΣX_i]`. -/
private theorem sur_efficiency_vs_systemLeastSquares_of_score_covariance
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hLS : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hQ_unit : IsUnit (systemPopulationGram μ X).det)
    (hscore : MemLp (fun ω => systemScore (X 0 ω) (e 0 ω)) 2 μ)
    (hmean : meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0)
    (hScoreCov :
      systemPopulationScoreCovariance μ X e =
        systemPopulationMiddle μ (fun ω => X 0 ω) Sigma)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance M).PosSemidef := by
  have hsys :=
    sur_efficiency_vs_systemLeastSquares_of_system_population_moments
      (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
      hGram hLS hSUR hSigma hSigma_unit hQ_unit hScoreCov hM hM_unit
  have hcov :
      covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω)) =
        systemPopulationScoreCovariance μ X e :=
    systemScore_covMat_eq_populationScoreCovariance
      (μ := μ) (X := X) (e := e) hscore hmean
  simpa [hcov] using hsys

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 system-population endpoint from
`SystemRegressionMomentConditions`.

`SystemRegressionMomentConditions` supplies the LS population Gram
integrability and nonsingularity. This endpoint keeps the homoskedastic
score-middle and SUR information identities explicit; the companion
`*_condExp_homoskedastic` wrappers discharge the score-middle identity from
`(11.8)`. -/
private theorem sur_efficiency_vs_systemLeastSquares_of_systemAssumption72
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hLS : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hScoreCov :
      systemPopulationScoreCovariance μ X e =
        systemPopulationMiddle μ (fun ω => X 0 ω) Sigma)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_vs_systemLeastSquares_of_system_population_moments
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72.gram_integrable hLS hSUR hSigma hSigma_unit h72.gram_nonsing
    hScoreCov hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 with the LS covariance written as `Var(X_i'e_i)`,
with the score-covariance and Gram facts projected from `SystemRegressionMomentConditions`. -/
private theorem sur_efficiency_vs_systemLeastSquares_scoreCov_of_systemAssumption72
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hLS : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hScoreCov :
      systemPopulationScoreCovariance μ X e =
        systemPopulationMiddle μ (fun ω => X 0 ω) Sigma)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_vs_systemLeastSquares_of_score_covariance
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72.gram_integrable hLS hSUR hSigma hSigma_unit h72.gram_nonsing
    h72.score_memLp h72.score_mean_zero hScoreCov hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 system-population endpoint from conditional
homoskedasticity `(11.8)`.

This is the same SUR-vs-LS comparison as
`sur_efficiency_vs_systemLeastSquares_of_system_population_moments`, but the
score-middle identity is discharged by
`systemPopulationScoreCovariance_eq_middle_of_condExp_homoskedastic` instead of
being assumed directly. -/
private theorem sur_efficiency_vs_systemLeastSquares_of_condExp_homoskedastic
    {ζ : Type*} [MeasurableSpace ζ] (Z : Ω → ζ) (hZ : Measurable Z)
    [SigmaFinite (μ.trim (conditioningSpace_le hZ))]
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hRobust : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hLS : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hX_meas : ∀ a c,
      AEStronglyMeasurable[conditioningSpace Z] (fun ω => X 0 ω a c) μ)
    (hee_int : ∀ a b, Integrable (fun ω => e 0 ω a * e 0 ω b) μ)
    (hWeightedError : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b)) μ)
    (hWeightedSigma : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma a b) μ)
    (hcond : ∀ a b,
      condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z =ᵐ[μ] fun _ => Sigma a b)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hQ_unit : IsUnit (systemPopulationGram μ X).det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef := by
  have hScoreCov :
      systemPopulationScoreCovariance μ X e =
        systemPopulationMiddle μ (fun ω => X 0 ω) Sigma :=
    systemPopulationScoreCovariance_eq_middle_of_condExp_homoskedastic
      (μ := μ) Z hZ X e Sigma hRobust hLS hX_meas hee_int
      hWeightedError hWeightedSigma hcond
  exact sur_efficiency_vs_systemLeastSquares_of_system_population_moments
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    hGram hLS hSUR hSigma hSigma_unit hQ_unit hScoreCov hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation endpoint from conditional
homoskedasticity `(11.8)`. -/
private theorem sur_efficiency_vs_systemLeastSquares_scoreCov_of_condExp_homoskedastic
    {ζ : Type*} [MeasurableSpace ζ] (Z : Ω → ζ) (hZ : Measurable Z)
    [SigmaFinite (μ.trim (conditioningSpace_le hZ))]
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hRobust : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hLS : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hX_meas : ∀ a c,
      AEStronglyMeasurable[conditioningSpace Z] (fun ω => X 0 ω a c) μ)
    (hee_int : ∀ a b, Integrable (fun ω => e 0 ω a * e 0 ω b) μ)
    (hWeightedError : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b)) μ)
    (hWeightedSigma : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma a b) μ)
    (hcond : ∀ a b,
      condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z =ᵐ[μ] fun _ => Sigma a b)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hQ_unit : IsUnit (systemPopulationGram μ X).det)
    (hscore : MemLp (fun ω => systemScore (X 0 ω) (e 0 ω)) 2 μ)
    (hmean : meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance M).PosSemidef := by
  have hScoreCov :
      systemPopulationScoreCovariance μ X e =
        systemPopulationMiddle μ (fun ω => X 0 ω) Sigma :=
    systemPopulationScoreCovariance_eq_middle_of_condExp_homoskedastic
      (μ := μ) Z hZ X e Sigma hRobust hLS hX_meas hee_int
      hWeightedError hWeightedSigma hcond
  exact sur_efficiency_vs_systemLeastSquares_of_score_covariance
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    hGram hLS hSUR hSigma hSigma_unit hQ_unit hscore hmean hScoreCov hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 from `SystemRegressionMomentConditions` and conditional
homoskedasticity `(11.8)`. `SystemRegressionMomentConditions` supplies the LS Gram and score
facts; the conditional-expectation bridge supplies the exact homoskedastic
score-middle identity. -/
private theorem sur_efficiency_vs_systemLeastSquares_of_systemAssumption72_condExp_homoskedastic
    {ζ : Type*} [MeasurableSpace ζ] (Z : Ω → ζ) (hZ : Measurable Z)
    [SigmaFinite (μ.trim (conditioningSpace_le hZ))]
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hLS : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hX_meas : ∀ a c,
      AEStronglyMeasurable[conditioningSpace Z] (fun ω => X 0 ω a c) μ)
    (hee_int : ∀ a b, Integrable (fun ω => e 0 ω a * e 0 ω b) μ)
    (hWeightedError : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω a * e 0 ω b)) μ)
    (hWeightedSigma : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma a b) μ)
    (hcond : ∀ a b,
      condExpOn μ (fun ω => e 0 ω a * e 0 ω b) Z =ᵐ[μ] fun _ => Sigma a b)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef := by
  exact sur_efficiency_vs_systemLeastSquares_of_condExp_homoskedastic
    (μ := μ) Z hZ M X e Sigma h72.gram_integrable
    (SystemRegressionMomentConditions.robustMiddleTerm_integrable (μ := μ) h72)
    hLS hSUR hX_meas hee_int hWeightedError hWeightedSigma hcond hSigma
    hSigma_unit h72.gram_nonsing hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 system-population endpoint from the packaged `(11.8)`
conditional homoskedasticity interface. -/
private theorem sur_efficiency_vs_systemLeastSquares_of_conditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hhom : SystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hQ_unit : IsUnit (systemPopulationGram μ X).det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_vs_systemLeastSquares_of_system_population_moments
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    hGram hhom.middle_integrable hSUR hSigma hSigma_unit hQ_unit
    hhom.scoreCovariance_eq_middle hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation endpoint from the packaged `(11.8)`
conditional homoskedasticity interface. -/
private theorem sur_efficiency_vs_systemLeastSquares_scoreCov_of_conditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hhom : SystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hQ_unit : IsUnit (systemPopulationGram μ X).det)
    (hscore : MemLp (fun ω => systemScore (X 0 ω) (e 0 ω)) 2 μ)
    (hmean : meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_vs_systemLeastSquares_of_score_covariance
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    hGram hhom.middle_integrable hSUR hSigma hSigma_unit hQ_unit
    hscore hmean hhom.scoreCovariance_eq_middle hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 from `SystemRegressionMomentConditions` and the packaged `(11.8)`
conditional homoskedasticity interface. -/
private theorem sur_efficiency_of_regression_hom
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : SystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_vs_systemLeastSquares_of_conditionalHomoskedasticity
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72.gram_integrable hhom hSUR hSigma hSigma_unit h72.gram_nonsing hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation endpoint from `SystemRegressionMomentConditions`
and the packaged `(11.8)` conditional homoskedasticity interface. -/
private theorem sur_scoreCov_efficiency_of_regression_hom
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : SystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_vs_systemLeastSquares_scoreCov_of_conditionalHomoskedasticity
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72.gram_integrable hhom hSUR hSigma hSigma_unit h72.gram_nonsing
    h72.score_memLp h72.score_mean_zero hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 from the literal matrix-valued `(11.8)` package. -/
private theorem sur_efficiency_vs_systemLeastSquares_of_matrix_conditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (hGram : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hQ_unit : IsUnit (systemPopulationGram μ X).det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_vs_systemLeastSquares_of_conditionalHomoskedasticity
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    hGram hhom.toSystemConditionalHomoskedasticity hSUR hSigma hSigma_unit
    hQ_unit hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 from `SystemRegressionMomentConditions` and the literal
matrix-valued `(11.8)` package. -/
private theorem sur_efficiency_of_matrix_regression_hom
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_of_regression_hom
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72 hhom.toSystemConditionalHomoskedasticity hSUR hSigma hSigma_unit hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation endpoint from `SystemRegressionMomentConditions`
and the literal matrix-valued `(11.8)` package. -/
private theorem sur_scoreCov_efficiency_of_matrix_regression_hom
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance M).PosSemidef :=
  sur_scoreCov_efficiency_of_regression_hom
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72 hhom.toSystemConditionalHomoskedasticity hSUR hSigma hSigma_unit hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 with the SUR information target derived exactly as
`E[Xᵢ'Σ⁻¹Xᵢ]`.

This is the literal matrix-valued `(11.8)` and Assumption 7.2 endpoint: callers
no longer supply a separate population information matrix `M`, the identity
`M = E[Xᵢ'Σ⁻¹Xᵢ]`, or its nonsingularity. -/
private theorem sur_efficiency_of_matrix_hom
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef :=
  sur_efficiency_of_matrix_regression_hom
    (μ := μ) (M := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])
    (X := X) (e := e) (Sigma := Sigma)
    h72 hhom hSUR hSigma hSigma_unit
    (surInformation_eq_systemPopulationMiddle X Sigma).symm
    (surInformation_nonsing_of_systemAssumption72 h72 hSUR hSigma hSigma_unit)

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation endpoint with the SUR information
target derived exactly as `E[Xᵢ'Σ⁻¹Xᵢ]`. -/
private theorem sur_scoreCov_efficiency_of_matrix_hom
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef :=
  sur_scoreCov_efficiency_of_matrix_regression_hom
    (μ := μ) (M := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])
    (X := X) (e := e) (Sigma := Sigma)
    h72 hhom hSUR hSigma hSigma_unit
    (surInformation_eq_systemPopulationMiddle X Sigma).symm
    (surInformation_nonsing_of_systemAssumption72 h72 hSUR hSigma hSigma_unit)

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
private theorem surCovariance_consistent_of_fixed_inverse_cov_wlln
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
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det) :
    TendstoInMeasure μ
      (fun t ω =>
        (systemSigmaHatStarObs
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
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ)
    (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        (systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹) μ :=
  aestronglyMeasurable_matrix_inv (hSigmaHat_meas t)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [DecidableEq m] in
/-- Measurability of a homoskedastic system middle with an estimated covariance
matrix, derived from coordinatewise finite-dimensional continuity. -/
theorem systemHomoskedasticMiddle_estimated_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {SigmaHat : ℕ → Ω → Matrix m m ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hSigmaHat_meas : ∀ t, AEStronglyMeasurable (SigmaHat t) μ)
    (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) (SigmaHat t ω)) μ := by
  simp only [systemHomoskedasticMiddle]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin t) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  have hXi : AEStronglyMeasurable (fun ω => X i.val ω) μ := hX_meas i.val
  have hXiT : AEStronglyMeasurable (fun ω => (X i.val ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXi
  have hLeft : AEStronglyMeasurable
      (fun ω => (X i.val ω)ᵀ * SigmaHat t ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXiT.prodMk (hSigmaHat_meas t))
  simpa [systemMiddleTerm, Matrix.mul_assoc] using
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hXi)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [DecidableEq m] in
/-- Measurability of the finite-sample weighted SUR score mean from
observation-level measurability of `X` and `Y`. -/
theorem surWeightedScoreMean_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ} (W : Matrix m m ℝ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        surWeightedScoreMean (fun i : Fin t => X i.val ω) W
          (fun i : Fin t => Y i.val ω)) μ := by
  simp only [surWeightedScoreMean]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin t) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  have hXi : AEStronglyMeasurable (fun ω => X i.val ω) μ := hX_meas i.val
  have hXiT : AEStronglyMeasurable (fun ω => (X i.val ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXi
  have hYi : AEStronglyMeasurable (fun ω => Y i.val ω) μ := hY_meas i.val
  have hWYi : AEStronglyMeasurable (fun ω => W *ᵥ Y i.val ω) μ :=
    (Continuous.matrix_mulVec continuous_const continuous_id).comp_aestronglyMeasurable hYi
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hXiT.prodMk hWYi)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [DecidableEq m] in
/-- Measurability of the finite-sample weighted SUR score mean with a random
weight matrix. -/
theorem surWeightedScoreMean_estimated_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {W : ℕ → Ω → Matrix m m ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hW_meas : ∀ t, AEStronglyMeasurable (W t) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        surWeightedScoreMean (fun i : Fin t => X i.val ω) (W t ω)
          (fun i : Fin t => Y i.val ω)) μ := by
  simp only [surWeightedScoreMean]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin t) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  have hXi : AEStronglyMeasurable (fun ω => X i.val ω) μ := hX_meas i.val
  have hXiT : AEStronglyMeasurable (fun ω => (X i.val ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXi
  have hYi : AEStronglyMeasurable (fun ω => Y i.val ω) μ := hY_meas i.val
  have hWYi : AEStronglyMeasurable (fun ω => W t ω *ᵥ Y i.val ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hW_meas t).prodMk hYi)
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hXiT.prodMk hWYi)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Measurability of the totalized SUR estimator with a random inverse-covariance
weight matrix. -/
theorem surBetaFromEstimatedInverseCovStar_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {W : ℕ → Ω → Matrix m m ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hW_meas : ∀ t, AEStronglyMeasurable (W t) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        surBetaFromInverseCovStar (fun i : Fin t => X i.val ω) (W t ω)
          (fun i : Fin t => Y i.val ω)) μ := by
  have hM : AEStronglyMeasurable
      (fun ω => systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) (W t ω)) μ :=
    systemHomoskedasticMiddle_estimated_aestronglyMeasurable
      (μ := μ) (X := X) (SigmaHat := W) hX_meas hW_meas t
  have hMinv : AEStronglyMeasurable
      (fun ω => (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) (W t ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hM
  have hScore : AEStronglyMeasurable
      (fun ω =>
        surWeightedScoreMean (fun i : Fin t => X i.val ω) (W t ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    surWeightedScoreMean_estimated_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) (W := W) hX_meas hW_meas hY_meas t
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hMinv.prodMk hScore)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Measurability of a scaled totalized SUR statistic with a random
inverse-covariance weight. -/
theorem surBetaFromEstimatedInverseCovStar_scaled_aemeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {W : ℕ → Ω → Matrix m m ℝ} (β : k → ℝ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hW_meas : ∀ t, AEStronglyMeasurable (W t) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar (fun i : Fin t => X i.val ω) (W t ω)
              (fun i : Fin t => Y i.val ω) - β)) μ := by
  have hβ : AEStronglyMeasurable
      (fun ω =>
        surBetaFromInverseCovStar (fun i : Fin t => X i.val ω) (W t ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    surBetaFromEstimatedInverseCovStar_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) (W := W) hX_meas hW_meas hY_meas t
  exact ((hβ.sub aestronglyMeasurable_const).const_smul (Real.sqrt (t : ℝ))).aemeasurable

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Measurability of the totalized fixed-weight SUR estimator from
observation-level measurability of `X` and `Y`. -/
theorem surBetaFromInverseCovStar_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ} (W : Matrix m m ℝ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        surBetaFromInverseCovStar (fun i : Fin t => X i.val ω) W
          (fun i : Fin t => Y i.val ω)) μ := by
  have hM : AEStronglyMeasurable
      (fun ω => systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W) μ := by
    simpa using
      systemHomoskedasticMiddle_estimated_aestronglyMeasurable
        (μ := μ) (X := X) (SigmaHat := fun _ _ => W)
        hX_meas (fun _ => aestronglyMeasurable_const) t
  have hMinv : AEStronglyMeasurable
      (fun ω => (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) W)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hM
  have hScore : AEStronglyMeasurable
      (fun ω =>
        surWeightedScoreMean (fun i : Fin t => X i.val ω) W
          (fun i : Fin t => Y i.val ω)) μ :=
    surWeightedScoreMean_aestronglyMeasurable (μ := μ) (X := X) (Y := Y)
      W hX_meas hY_meas t
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hMinv.prodMk hScore)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Measurability of Hansen Theorem 11.4's scaled fixed-weight SUR statistic. -/
theorem surBetaFromInverseCovStar_scaled_aemeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ} (W : Matrix m m ℝ) (β : k → ℝ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar (fun i : Fin t => X i.val ω) W
              (fun i : Fin t => Y i.val ω) - β)) μ := by
  have hβ : AEStronglyMeasurable
      (fun ω =>
        surBetaFromInverseCovStar (fun i : Fin t => X i.val ω) W
          (fun i : Fin t => Y i.val ω)) μ :=
    surBetaFromInverseCovStar_aestronglyMeasurable (μ := μ) (X := X) (Y := Y)
      W hX_meas hY_meas t
  exact ((hβ.sub aestronglyMeasurable_const).const_smul (Real.sqrt (t : ℝ))).aemeasurable

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Measurability of Hansen Theorem 11.4's scaled fixed-error-covariance SUR
statistic. -/
theorem surBetaFromErrorCovStar_scaled_aemeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ} (Sigma : Matrix m m ℝ)
    (β : k → ℝ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromErrorCovStar (fun i : Fin t => X i.val ω) Sigma
              (fun i : Fin t => Y i.val ω) - β)) μ := by
  simpa [surBetaFromErrorCovStar] using
    surBetaFromInverseCovStar_scaled_aemeasurable
      (μ := μ) (X := X) (Y := Y) Sigma⁻¹ β hX_meas hY_meas t

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Hansen Theorem 11.4 fixed-weight SUR wrapper with statistic measurability
derived from observation-level measurability of `X` and `Y`. -/
private theorem surBetaFromInverseCovStar_tendstoInDistribution_of_observation_measurable
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {W : Matrix m m ℝ} {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X W e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) W (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (surAsymptoticVariance M)) :=
  surBetaFromInverseCovStar_tendstoInDistribution
    (μ := μ) (X := X) (e := e) (Y := Y) (W := W) (M := M)
    h β hmodel
    (fun t =>
      surBetaFromInverseCovStar_scaled_aemeasurable
        (μ := μ) (X := X) (Y := Y) W β hX_meas hY_meas t)

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 fixed-error-covariance SUR wrapper with statistic
measurability derived from observation-level measurability of `X` and `Y`. -/
theorem surBetaFromErrorCovStar_tendstoInDistribution_of_observation_measurable
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromErrorCovStar
            (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (surAsymptoticVariance M)) :=
  surBetaFromErrorCovStar_tendstoInDistribution
    (μ := μ) (X := X) (e := e) (Y := Y) (Sigma := Sigma) (M := M)
    h β hmodel
    (fun t =>
      surBetaFromErrorCovStar_scaled_aemeasurable
        (μ := μ) (X := X) (Y := Y) Sigma β hX_meas hY_meas t)

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 estimated-inverse-covariance SUR wrapper from a
fixed-`Σ` SUR CLT and an explicit feasible-weight substitution.

This is the reusable Slutsky step for feasible SUR beta estimators. The premise
`hsub` is exactly the scaled `oₚ(1)` gap between the estimator using the random
inverse-covariance sequence `SigmaInvHat` and the fixed-error-covariance
estimator using `Σ⁻¹`. -/
private theorem surEstimatedWeight_tendsto_of_fixed_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {SigmaInvHat : ℕ → Ω → Matrix m m ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0))
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hSigmaInvHat_meas : ∀ t, AEStronglyMeasurable (SigmaInvHat t) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (surAsymptoticVariance M)) :=
  tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (surBetaFromErrorCovStar
          (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
    (Y := fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (surBetaFromInverseCovStar
          (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)
          (fun i : Fin t => Y i.val ω) - β))
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    (surBetaFromErrorCovStar_tendstoInDistribution_of_observation_measurable
      (μ := μ) (X := X) (e := e) (Y := Y) Sigma h β hmodel hX_meas hY_meas)
    hsub
    (fun t =>
      surBetaFromEstimatedInverseCovStar_scaled_aemeasurable
        (μ := μ) (X := X) (Y := Y) (W := SigmaInvHat) β
        hX_meas hSigmaInvHat_meas hY_meas t)

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 fixed-error-covariance SUR wrapper from weighted-score
moment primitives.

This specializes the reusable fixed-weight score package at `W = Σ⁻¹`, pins the
population covariance to Hansen's `E[Xᵢ'Σ⁻¹Xᵢ]`, and derives statistic
measurability from observation-level measurability of `X` and `Y`. The remaining
theorem-facing stochastic content is the weighted score covariance identity,
which should be discharged from conditional homoskedasticity `(11.8)`. -/
theorem surBetaFromErrorCovStar_tendstoInDistribution_of_weighted_score_moments
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) (β : k → ℝ)
    (hinfo_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hinfo_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hinfo_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hscore_iIndep : iIndepFun
      (fun i ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω)) μ)
    (hscore_ident : ∀ i,
      IdentDistrib
        (fun ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω))
        (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hscore_cov :
      covMat μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) =
        μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])
    (hinfo_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromErrorCovStar
            (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (surAsymptoticVariance
          (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))) := by
  have hcond :
      SURScoreCLTConditions μ X Sigma⁻¹ e
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]) :=
    SURScoreCLTConditions.of_weighted_score_moments
      (μ := μ) (X := X) (e := e) (W := Sigma⁻¹)
      hinfo_int hinfo_indep hinfo_ident hscore_memLp hscore_iIndep
      hscore_ident hscore_mean_zero hscore_cov hinfo_unit
      (Matrix.PosSemidef.inv hSigma_posSemidef)
  exact surBetaFromErrorCovStar_tendstoInDistribution_of_observation_measurable
    (μ := μ) (X := X) (e := e) (Y := Y) (Sigma := Sigma)
    (M := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])
    hcond β hmodel hX_meas hY_meas

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype k]
  [DecidableEq k] [DecidableEq m] in
/-- Measurability of the normalized system score mean from observation-level
measurability. -/
private theorem systemScoreMean_observation_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω => systemScoreMean (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω)) μ := by
  classical
  simpa [surWeightedScoreMean, systemScoreMean, systemScore] using
    surWeightedScoreMean_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) (W := (1 : Matrix m m ℝ))
      hX_meas hY_meas t

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype k]
  [DecidableEq k] [DecidableEq m] in
/-- Measurability of the normalized system Gram from observation-level
measurability. -/
private theorem systemNormalizedGram_observation_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω => systemNormalizedGram (fun i : Fin t => X i.val ω)) μ := by
  classical
  have hMiddle :
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((fun _ : ℕ => fun _ : Ω => (1 : Matrix m m ℝ)) t ω)) μ :=
    systemHomoskedasticMiddle_estimated_aestronglyMeasurable
      (μ := μ) (X := X)
      (SigmaHat := fun _ _ => (1 : Matrix m m ℝ))
      hX_meas (fun _ => aestronglyMeasurable_const) t
  simpa [systemNormalizedGram, systemHomoskedasticMiddle, systemMiddleTerm] using hMiddle

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Measurability of the totalized observation-level system LS estimator from
observation-level measurability. -/
theorem systemLeastSquaresBetaStarObs_observation_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemLeastSquaresBetaStarObs (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ := by
  have hQ : AEStronglyMeasurable
      (fun ω => systemNormalizedGram (fun i : Fin t => X i.val ω)) μ :=
    systemNormalizedGram_observation_aestronglyMeasurable
      (μ := μ) (X := X) hX_meas t
  have hQinv : AEStronglyMeasurable
      (fun ω => (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hQ
  have hg : AEStronglyMeasurable
      (fun ω => systemScoreMean (fun i : Fin t => X i.val ω)
        (fun i : Fin t => Y i.val ω)) μ :=
    systemScoreMean_observation_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t
  have hRhs : AEStronglyMeasurable
      (fun ω =>
        (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
          systemScoreMean (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQinv.prodMk hg)
  refine hRhs.congr (ae_of_all μ (fun ω => ?_))
  exact (systemLeastSquaresBetaStarObs_eq_normalized_moments
    (X := fun i : Fin t => X i.val ω) (Y := fun i : Fin t => Y i.val ω)).symm

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Measurability of the actual feasible SUR residual covariance
`Σ̂ = n⁻¹∑ êᵢêᵢ'`, derived from observation-level measurability of `X` and `Y`. -/
theorem surResidualCovarianceStarObs_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ := by
  have hBeta : AEStronglyMeasurable
      (fun ω =>
        systemLeastSquaresBetaStarObs (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω)) μ :=
    systemLeastSquaresBetaStarObs_observation_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t
  have houter_cont : Continuous (fun v : m → ℝ => Matrix.vecMulVec v v) := by
    refine continuous_pi (fun a => ?_)
    refine continuous_pi (fun b => ?_)
    simpa [Matrix.vecMulVec_apply] using
      (continuous_apply a).mul (continuous_apply b)
  simp only [systemSigmaHatStarObs, systemSigmaHat]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin t) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  have hYi : AEStronglyMeasurable (fun ω => Y i.val ω) μ := hY_meas i.val
  have hXi : AEStronglyMeasurable (fun ω => X i.val ω) μ := hX_meas i.val
  have hFit : AEStronglyMeasurable
      (fun ω =>
        X i.val ω *ᵥ
          systemLeastSquaresBetaStarObs (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXi.prodMk hBeta)
  have hRes : AEStronglyMeasurable
      (fun ω =>
        systemResidualStarObs (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) i) μ := by
    refine (hYi.sub hFit).congr (ae_of_all μ (fun ω => ?_))
    ext j
    simp [systemResidualStarObs_apply, systemFittedStarObs, Matrix.mulVec]
  exact houter_cont.comp_aestronglyMeasurable hRes

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Measurability of Hansen's feasible SUR estimator
`(n⁻¹∑ Xᵢ'Σ̂⁻¹Xᵢ)⁻¹(n⁻¹∑ Xᵢ'Σ̂⁻¹Yᵢ)`. -/
theorem surBetaEstimatorStarObs_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        surBetaEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ := by
  let SigmaInvHat : ℕ → Ω → Matrix m m ℝ := fun t ω =>
    (systemSigmaHatStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹
  have hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ :=
    fun t => surResidualCovarianceStarObs_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t
  have hSigmaInvHat_meas : ∀ t, AEStronglyMeasurable (SigmaInvHat t) μ := by
    intro t
    exact surResidualCovarianceStarObs_inverse_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hSigmaHat_meas t
  simpa [surBetaEstimatorStarObs, SigmaInvHat] using
    surBetaFromEstimatedInverseCovStar_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) (W := SigmaInvHat)
      hX_meas hSigmaInvHat_meas hY_meas t

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Measurability of Hansen Theorem 11.4's scaled feasible SUR statistic. -/
private theorem surBetaEstimatorStarObs_scaled_aemeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ} (β : k → ℝ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) (t : ℕ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ := by
  have hβ : AEStronglyMeasurable
      (fun ω =>
        surBetaEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ :=
    surBetaEstimatorStarObs_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t
  exact ((hβ.sub aestronglyMeasurable_const).const_smul (Real.sqrt (t : ℝ))).aemeasurable

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Random-weight SUR Star-estimator linearization.

This is the random-covariance counterpart of
`surBetaFromInverseCovStar_linearization`.  It closes the singular-information
part of the feasible SUR beta substitution whenever the estimated SUR
information matrix converges in probability to a nonsingular population matrix.
-/
theorem surBetaFromEstimatedInverseCovStar_linearization
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {SigmaInvHat : ℕ → Ω → Matrix m m ℝ} {M : Matrix k k ℝ}
    (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hMhat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω)) μ)
    (hMhat_tendsto : TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          (SigmaInvHat t ω))
      atTop (fun _ => M))
    (hM_unit : IsUnit M.det) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
              (SigmaInvHat t ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω)
                (SigmaInvHat t ω) (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  exact surBetaFromInverseCovStar_linearization_core
    (μ := μ) (X := X) (e := e) (Y := Y)
    (SigmaInvHat := SigmaInvHat) (M := M) β hmodel
    hMhat_meas hMhat_tendsto hM_unit

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Weighted-score substitution from inverse-covariance consistency and bounded
scaled scalar score weights.

This is the finite-sum stochastic-order bridge for Hansen Theorem 11.4:
`Σ̂⁻¹ ->p Σ⁻¹` and
`√n n⁻¹∑ X_iaj e_ib = Oₚ(1)` coordinatewise imply
`√n(ĝ_{Σ̂⁻¹}-ĝ_{Σ⁻¹}) = oₚ(1)`. -/
theorem surWeightedScoreMean_substitution_of_inverseCovariance_bounded_score_weights
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {SigmaInvHat : ℕ → Ω → Matrix m m ℝ} {SigmaInv : Matrix m m ℝ}
    (hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => SigmaInv))
    (hScoreWeight : ∀ a b : m, ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          Real.sqrt (t : ℝ) *
            surWeightedScoreScalarWeight
              (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω) (fun i : Fin t => e i.val ω)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) SigmaInv
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_pi (μ := μ) (fun j => ?_)
  have hOuter : ∀ a ∈ (Finset.univ : Finset m),
      TendstoInMeasure μ
        (fun t ω => ∑ b : m,
          (SigmaInvHat t ω a b - SigmaInv a b) *
            (Real.sqrt (t : ℝ) *
              surWeightedScoreScalarWeight
                (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j))
        atTop (fun _ => 0) := by
    intro a _
    have hInner : ∀ b ∈ (Finset.univ : Finset m),
        TendstoInMeasure μ
          (fun t ω =>
            (SigmaInvHat t ω a b - SigmaInv a b) *
              (Real.sqrt (t : ℝ) *
                surWeightedScoreScalarWeight
                  (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j))
          atTop (fun _ => 0) := by
      intro b _
      have hSigma_ab : TendstoInMeasure μ
          (fun t ω => SigmaInvHat t ω a b) atTop (fun _ => SigmaInv a b) := by
        simpa using TendstoInMeasure.pi_apply
          (TendstoInMeasure.pi_apply hSigmaInvHat a) b
      have hdiff_ab : TendstoInMeasure μ
          (fun t ω => SigmaInvHat t ω a b - SigmaInv a b)
          atTop (fun _ => 0) :=
        TendstoInMeasure.sub_limit_zero_real hSigma_ab
      exact TendstoInMeasure.mul_boundedInProbability hdiff_ab
        (hScoreWeight a b j)
    simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset m))
      (X := fun b t ω =>
        (SigmaInvHat t ω a b - SigmaInv a b) *
          (Real.sqrt (t : ℝ) *
            surWeightedScoreScalarWeight
              (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j))
      hInner
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset m))
    (X := fun a t ω => ∑ b : m,
      (SigmaInvHat t ω a b - SigmaInv a b) *
        (Real.sqrt (t : ℝ) *
          surWeightedScoreScalarWeight
            (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j))
    hOuter
  refine hsum.congr_left (fun t => ae_of_all μ (fun ω => ?_))
  simpa using
    (surWeightedScoreMean_scaled_sub_apply_eq_sum_weight
      (root := Real.sqrt (t : ℝ))
      (X := fun i : Fin t => X i.val ω) (W := SigmaInvHat t ω)
      (V := SigmaInv) (e := fun i : Fin t => e i.val ω) (j := j)).symm

omit [Fintype n] [DecidableEq n] in
/-- Residual-covariance specialization of the weighted-score substitution
bridge for Hansen Theorem 11.4.

This turns residual covariance consistency `Σ̂ ->p Σ` into inverse-covariance
consistency by inverse CMT, then applies the scalar finite-sum score bridge. -/
theorem surWeightedScoreMean_substitution_of_residualCovariance_bounded_score_weights
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det)
    (hScoreWeight : ∀ a b : m, ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          Real.sqrt (t : ℝ) *
            surWeightedScoreScalarWeight
              (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω)
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
            (fun i : Fin t => e i.val ω)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0) := by
  let SigmaInvHat : ℕ → Ω → Matrix m m ℝ := fun t ω =>
    (systemSigmaHatStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹
  have hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ :=
    fun t => surResidualCovarianceStarObs_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t
  have hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => Sigma⁻¹) := by
    simpa [SigmaInvHat] using
      surResidualCovarianceStarObs_inverse_tendstoInMeasure
        (μ := μ) (X := X) (Y := Y) (Sigma := Sigma)
        hSigmaHat_meas hSigmaHat hSigma_unit
  simpa [SigmaInvHat] using
    surWeightedScoreMean_substitution_of_inverseCovariance_bounded_score_weights
      (μ := μ) (X := X) (e := e) (SigmaInvHat := SigmaInvHat)
      (SigmaInv := Sigma⁻¹) hSigmaInvHat hScoreWeight

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Fixed-weight scaled SUR score coordinates are bounded in probability under
the fixed-weight score CLT package. -/
theorem surWeightedScoreMean_fixed_boundedInProbability_of_score_limit
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {W : Matrix m m ℝ} {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X W e M) (j : k) :
    BoundedInProbability μ
      (fun t ω =>
        (Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω) W
            (fun i : Fin t => e i.val ω)) j) := by
  have hcoord := h.score_limit.continuous_comp (continuous_apply j)
  exact BoundedInProbability.of_tendstoInDistribution
    (by simpa [Function.comp_def] using hcoord)

omit [Fintype n] [DecidableEq n] in
/-- Linearized SUR leading-term substitution from score substitution.

This is the stochastic-order bridge behind the feasible-weight step in Hansen
Theorem 11.4.  Once the estimated inverse covariance is consistent, the two
inverse-information matrices share the same probability limit.  Therefore the
whole leading term differs by `oₚ(1)` if the random-weight score is
asymptotically equivalent to the fixed-`Σ⁻¹` score and the fixed score is
coordinatewise `Oₚ(1)`. -/
theorem surLinearizedScore_substitution_of_inverseCovariance_score_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {SigmaInvHat : ℕ → Ω → Matrix m m ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hSigmaInvHat_meas : ∀ t, AEStronglyMeasurable (SigmaInvHat t) μ)
    (hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => Sigma⁻¹))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hscore_sub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω) (fun i : Fin t => e i.val ω)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0))
    (hscore_bounded : ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          (Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
              (fun i : Fin t => e i.val ω)) j)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω))⁻¹ *ᵥ
          (Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω)
              (SigmaInvHat t ω) (fun i : Fin t => e i.val ω))) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  let Ahat : ℕ → Ω → Matrix k k ℝ := fun t ω =>
    (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
      (SigmaInvHat t ω))⁻¹
  let Bhat : ℕ → Ω → Matrix k k ℝ := fun t ω =>
    (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)⁻¹
  let Shat : ℕ → Ω → k → ℝ := fun t ω =>
    Real.sqrt (t : ℝ) •
      surWeightedScoreMean (fun i : Fin t => X i.val ω)
        (SigmaInvHat t ω) (fun i : Fin t => e i.val ω)
  let Sfixed : ℕ → Ω → k → ℝ := fun t ω =>
    Real.sqrt (t : ℝ) •
      surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
        (fun i : Fin t => e i.val ω)
  have hMhat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω)) μ :=
    systemHomoskedasticMiddle_estimated_aestronglyMeasurable
      (μ := μ) (X := X) (SigmaHat := SigmaInvHat)
      hX_meas hSigmaInvHat_meas
  have hMhat_tendsto : TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          (SigmaInvHat t ω))
      atTop (fun _ => M) :=
    SystemFeasible.middle_of_covariance_bounded_weights
      (μ := μ) (X := X) (Sigma := Sigma⁻¹)
      (SigmaHat := SigmaInvHat) (Omega := M)
      h.information_tendsto hSigmaInvHat hWeight
  have hAhat_meas : ∀ t, AEStronglyMeasurable (Ahat t) μ :=
    fun t => aestronglyMeasurable_matrix_inv (hMhat_meas t)
  have hShat_meas : ∀ t, AEStronglyMeasurable (Shat t) μ := by
    intro t
    exact (surWeightedScoreMean_estimated_aestronglyMeasurable
      (μ := μ) (X := X) (Y := e) (W := SigmaInvHat)
      hX_meas hSigmaInvHat_meas he_meas t).const_smul (Real.sqrt (t : ℝ))
  have hSfixed_meas : ∀ t, AEStronglyMeasurable (Sfixed t) μ := by
    intro t
    exact (surWeightedScoreMean_aestronglyMeasurable
      (μ := μ) (X := X) (Y := e) (W := Sigma⁻¹)
      hX_meas he_meas t).const_smul (Real.sqrt (t : ℝ))
  have hAhat : TendstoInMeasure μ Ahat atTop (fun _ => M⁻¹) := by
    simpa [Ahat] using
      tendstoInMeasure_matrix_inv hMhat_meas hMhat_tendsto
        (fun _ => h.information_nonsing)
  have hBhat : TendstoInMeasure μ Bhat atTop (fun _ => M⁻¹) := by
    simpa [Bhat] using
      tendstoInMeasure_matrix_inv h.information_meas h.information_tendsto
        (fun _ => h.information_nonsing)
  have hscore_sub' :
      TendstoInMeasure μ (fun t ω => Shat t ω - Sfixed t ω)
        atTop (fun _ => 0) := by
    simpa [Shat, Sfixed] using hscore_sub
  have hmain :=
    randomMatrix_mulVec_substitution_tendstoInMeasure_zero
      (μ := μ) (Ahat := Ahat) (Bhat := Bhat) (A := M⁻¹)
      (T := Shat) (S := Sfixed)
      hAhat_meas hShat_meas hSfixed_meas hAhat hBhat hscore_sub'
      (by simpa [Sfixed] using hscore_bounded)
  simpa [Ahat, Bhat, Shat, Sfixed] using hmain

omit [Fintype n] [DecidableEq n] in
/-- Feasible SUR beta substitution from random-weight information convergence
and the linearized score substitution.

The theorem reduces Hansen Theorem 11.4's rate-sensitive feasible
`Σ̂⁻¹` beta gap to the corresponding gap between the two linearized SUR score
terms.  The estimated information convergence is derived from
`Σ̂⁻¹ ->p Σ⁻¹` and bounded empirical design weights; the totalized
normal-equation remainders are handled internally by
`surBetaFromEstimatedInverseCovStar_linearization` and the fixed-`Σ` companion.
-/
theorem surBetaFromEstimatedInverseCovStar_substitution_of_inverseCovariance_linearized
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {SigmaInvHat : ℕ → Ω → Matrix m m ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hSigmaInvHat_meas : ∀ t, AEStronglyMeasurable (SigmaInvHat t) μ)
    (hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => Sigma⁻¹))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hlinearized : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω))⁻¹ *ᵥ
          (Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω)
              (SigmaInvHat t ω) (fun i : Fin t => e i.val ω))) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0) := by
  have hMhat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω)) μ :=
    systemHomoskedasticMiddle_estimated_aestronglyMeasurable
      (μ := μ) (X := X) (SigmaHat := SigmaInvHat)
      hX_meas hSigmaInvHat_meas
  have hMhat_tendsto : TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          (SigmaInvHat t ω))
      atTop (fun _ => M) :=
    SystemFeasible.middle_of_covariance_bounded_weights
      (μ := μ) (X := X) (Sigma := Sigma⁻¹)
      (SigmaHat := SigmaInvHat) (Omega := M)
      h.information_tendsto hSigmaInvHat hWeight
  have hEstimated :=
    surBetaFromEstimatedInverseCovStar_linearization
      (μ := μ) (X := X) (e := e) (Y := Y)
      (SigmaInvHat := SigmaInvHat) (M := M) β hmodel
      hMhat_meas hMhat_tendsto h.information_nonsing
  have hFixed :=
    surBetaFromErrorCovStar_linearization
      (μ := μ) (X := X) (e := e) (Y := Y)
      Sigma h β hmodel
  refine tendstoInMeasure_pi (fun a => ?_)
  have hEstimated_a := TendstoInMeasure.pi_apply hEstimated a
  have hLinearized_a := TendstoInMeasure.pi_apply hlinearized a
  have hFixed_a := TendstoInMeasure.pi_apply hFixed a
  have hsum :=
    TendstoInMeasure.add_zero_real
      (TendstoInMeasure.add_zero_real hEstimated_a hLinearized_a)
      (TendstoInMeasure.neg_zero_real hFixed_a)
  refine hsum.congr_left (fun t => ae_of_all μ (fun ω => ?_))
  simp only [Pi.sub_apply, Pi.smul_apply]
  ring

omit [Fintype n] [DecidableEq n] in
/-- Feasible SUR beta substitution from estimated inverse-covariance consistency
and score-level substitution.

Compared with
`surBetaFromEstimatedInverseCovStar_substitution_of_inverseCovariance_linearized`,
this wrapper discharges the linearized leading-term premise from the
coordinatewise tightness of the fixed-`Σ⁻¹` score and the score-level
substitution `√n(ĝ_{Σ̂⁻¹}-ĝ_{Σ⁻¹}) = oₚ(1)`. -/
theorem surBetaFromEstimatedInverseCovStar_substitution_of_inverseCovariance_score
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {SigmaInvHat : ℕ → Ω → Matrix m m ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hSigmaInvHat_meas : ∀ t, AEStronglyMeasurable (SigmaInvHat t) μ)
    (hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => Sigma⁻¹))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hscore_sub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω)
            (SigmaInvHat t ω) (fun i : Fin t => e i.val ω)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0))
    (hscore_bounded : ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          (Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
              (fun i : Fin t => e i.val ω)) j)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromInverseCovStar
            (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0) := by
  have hlinearized :=
    surLinearizedScore_substitution_of_inverseCovariance_score_substitution
      (μ := μ) (X := X) (e := e) (SigmaInvHat := SigmaInvHat)
      Sigma h hX_meas he_meas hSigmaInvHat_meas hSigmaInvHat
      hWeight hscore_sub hscore_bounded
  exact
    surBetaFromEstimatedInverseCovStar_substitution_of_inverseCovariance_linearized
      (μ := μ) (X := X) (e := e) (Y := Y)
      (SigmaInvHat := SigmaInvHat) Sigma h β hmodel hX_meas
      hSigmaInvHat_meas hSigmaInvHat hWeight hlinearized

omit [Fintype n] [DecidableEq n] in
/-- Hansen-facing feasible SUR beta substitution for the actual residual
covariance estimator.

This specializes
`surBetaFromEstimatedInverseCovStar_substitution_of_inverseCovariance_linearized`
to `Σ̂ = systemSigmaHatStarObs X Y`, deriving `Σ̂⁻¹ ->p Σ⁻¹` from
residual-covariance consistency and inverse CMT.
-/
private theorem surBetaEstimatorStarObs_substitution_of_residualCovariance_linearized
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det)
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hlinearized : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹))⁻¹ *ᵥ
          (Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω)
              ((systemSigmaHatStarObs
                (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
              (fun i : Fin t => e i.val ω))) -
        fun (t : ℕ) ω =>
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0) := by
  let SigmaInvHat : ℕ → Ω → Matrix m m ℝ := fun t ω =>
    (systemSigmaHatStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹
  have hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ :=
    fun t => surResidualCovarianceStarObs_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t
  have hSigmaInvHat_meas : ∀ t, AEStronglyMeasurable (SigmaInvHat t) μ := by
    intro t
    exact surResidualCovarianceStarObs_inverse_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hSigmaHat_meas t
  have hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => Sigma⁻¹) := by
    simpa [SigmaInvHat] using
      surResidualCovarianceStarObs_inverse_tendstoInMeasure
        (μ := μ) (X := X) (Y := Y) (Sigma := Sigma)
        hSigmaHat_meas hSigmaHat hSigma_unit
  simpa [surBetaEstimatorStarObs, SigmaInvHat] using
    surBetaFromEstimatedInverseCovStar_substitution_of_inverseCovariance_linearized
      (μ := μ) (X := X) (e := e) (Y := Y)
      (SigmaInvHat := SigmaInvHat) Sigma h β hmodel
      hX_meas hSigmaInvHat_meas hSigmaInvHat hWeight
      (by simpa [SigmaInvHat] using hlinearized)

omit [Fintype n] [DecidableEq n] in
/-- Hansen-facing feasible SUR beta substitution from the residual-covariance
score substitution.

This specializes the score-level substitution bridge to Hansen's actual
residual covariance estimator `Σ̂ = n⁻¹∑ êᵢêᵢ'`.  The remaining stochastic
premise is now the scaled weighted-score substitution
`√n(ĝ_{Σ̂⁻¹}-ĝ_{Σ⁻¹}) = oₚ(1)`, rather than the full beta-level or
linearized leading-term gap. -/
theorem surBetaEstimatorStarObs_substitution_of_residualCovariance_score
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det)
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hscore_sub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          surWeightedScoreMean (fun i : Fin t => X i.val ω)
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
            (fun i : Fin t => e i.val ω)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0))
    (hscore_bounded : ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          (Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
              (fun i : Fin t => e i.val ω)) j)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0) := by
  let SigmaInvHat : ℕ → Ω → Matrix m m ℝ := fun t ω =>
    (systemSigmaHatStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹
  have hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ :=
    fun t => surResidualCovarianceStarObs_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t
  have hSigmaInvHat_meas : ∀ t, AEStronglyMeasurable (SigmaInvHat t) μ := by
    intro t
    exact surResidualCovarianceStarObs_inverse_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hSigmaHat_meas t
  have hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => Sigma⁻¹) := by
    simpa [SigmaInvHat] using
      surResidualCovarianceStarObs_inverse_tendstoInMeasure
        (μ := μ) (X := X) (Y := Y) (Sigma := Sigma)
        hSigmaHat_meas hSigmaHat hSigma_unit
  simpa [surBetaEstimatorStarObs, SigmaInvHat] using
    surBetaFromEstimatedInverseCovStar_substitution_of_inverseCovariance_score
      (μ := μ) (X := X) (e := e) (Y := Y)
      (SigmaInvHat := SigmaInvHat) Sigma h β hmodel
      hX_meas he_meas hSigmaInvHat_meas hSigmaInvHat hWeight
      (by simpa [SigmaInvHat] using hscore_sub) hscore_bounded

omit [Fintype n] [DecidableEq n] in
/-- Hansen-facing feasible SUR beta substitution from residual-covariance
consistency and bounded scaled scalar score weights.

This composes the finite-sum score-substitution bridge with
`surBetaEstimatorStarObs_substitution_of_residualCovariance_score`, so callers
no longer need to supply `√n(ĝ_{Σ̂⁻¹}-ĝ_{Σ⁻¹}) = oₚ(1)` directly. -/
theorem surBetaEstimatorStarObs_substitution_of_residualCovariance_bounded_score_weights
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det)
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hScoreWeight : ∀ a b : m, ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          Real.sqrt (t : ℝ) *
            surWeightedScoreScalarWeight
              (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0) := by
  have hscore_sub :=
    surWeightedScoreMean_substitution_of_residualCovariance_bounded_score_weights
      (μ := μ) (X := X) (e := e) (Y := Y) Sigma
      hX_meas hY_meas hSigmaHat hSigma_unit hScoreWeight
  have hscore_bounded : ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          (Real.sqrt (t : ℝ) •
            surWeightedScoreMean (fun i : Fin t => X i.val ω) Sigma⁻¹
              (fun i : Fin t => e i.val ω)) j) :=
    fun j =>
      surWeightedScoreMean_fixed_boundedInProbability_of_score_limit
        (μ := μ) (X := X) (e := e) (W := Sigma⁻¹) (M := M) h j
  exact
    surBetaEstimatorStarObs_substitution_of_residualCovariance_score
      (μ := μ) (X := X) (e := e) (Y := Y) Sigma h β hmodel
      hX_meas he_meas hY_meas hSigmaHat hSigma_unit hWeight
      hscore_sub hscore_bounded

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 for the named feasible SUR estimator, from the
fixed-`Σ` SUR CLT and the feasible residual-covariance substitution.

The premise `hsub` is the scaled `oₚ(1)` gap between Hansen's actual feasible
SUR estimator using `Σ̂⁻¹` and the fixed-error-covariance estimator using
`Σ⁻¹`. -/
theorem surBetaEstimatorStarObs_tendstoInDistribution_of_fixed_weight_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) {M : Matrix k k ℝ}
    (h : SURScoreCLTConditions μ X Sigma⁻¹ e M) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0))
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (surAsymptoticVariance M)) := by
  let SigmaInvHat : ℕ → Ω → Matrix m m ℝ := fun t ω =>
    (systemSigmaHatStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹
  have hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ :=
    fun t => surResidualCovarianceStarObs_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t
  have hSigmaInvHat_meas : ∀ t, AEStronglyMeasurable (SigmaInvHat t) μ := by
    intro t
    exact surResidualCovarianceStarObs_inverse_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hSigmaHat_meas t
  simpa [surBetaEstimatorStarObs, SigmaInvHat] using
    surEstimatedWeight_tendsto_of_fixed_substitution
      (μ := μ) (X := X) (e := e) (Y := Y) (SigmaInvHat := SigmaInvHat)
      Sigma h β hmodel (by simpa [surBetaEstimatorStarObs, SigmaInvHat] using hsub)
      hX_meas hSigmaInvHat_meas hY_meas

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 feasible SUR wrapper from weighted-score moment
primitives and the feasible residual-covariance substitution.

This is the feasible counterpart of
`surBetaFromErrorCovStar_tendstoInDistribution_of_weighted_score_moments`.
The weighted-score covariance identity remains an explicit theorem-facing
premise until the repo has a literal matrix conditional-homoskedasticity
package for (11.8). -/
theorem surBetaEstimatorStarObs_tendstoInDistribution_of_weighted_score_moments
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ) (β : k → ℝ)
    (hinfo_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hinfo_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hinfo_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hscore_iIndep : iIndepFun
      (fun i ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω)) μ)
    (hscore_ident : ∀ i,
      IdentDistrib
        (fun ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω))
        (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hscore_cov :
      covMat μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) =
        μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])
    (hinfo_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0))
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (surAsymptoticVariance
          (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))) := by
  have hcond :
      SURScoreCLTConditions μ X Sigma⁻¹ e
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]) :=
    SURScoreCLTConditions.of_weighted_score_moments
      (μ := μ) (X := X) (e := e) (W := Sigma⁻¹)
      hinfo_int hinfo_indep hinfo_ident hscore_memLp hscore_iIndep
      hscore_ident hscore_mean_zero hscore_cov hinfo_unit
      (Matrix.PosSemidef.inv hSigma_posSemidef)
  exact surBetaEstimatorStarObs_tendstoInDistribution_of_fixed_weight_substitution
    (μ := μ) (X := X) (e := e) (Y := Y) Sigma hcond β hmodel hsub hX_meas hY_meas

omit [Fintype n] [DecidableEq n] in
/-- Theorem-facing condition package for Hansen Theorem 11.4.

The conclusion is the Gaussian limit of Hansen's named feasible SUR estimator
using `Σ̂⁻¹`. The package keeps two currently primitive steps explicit:

* `score_covariance_identity` is the weighted score-covariance identity
  expected from conditional homoskedasticity `(11.8)`;
* `feasible_weight_substitution` is the scaled `oₚ(1)` replacement of fixed
  `Σ⁻¹` by the feasible residual-covariance inverse `Σ̂⁻¹`.

All remaining fields are the existing iid score/WLLN, nonsingularity, and
measurability hypotheses consumed by the fixed-weight SUR machinery above. -/
structure SURGaussianLimitConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (e Y : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ) (β : k → ℝ) : Prop where
  x_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (X i) μ
  y_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (Y i) μ
  information_integrable : Integrable
    (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ
  information_independent : Pairwise ((· ⟂ᵢ[μ] ·) on
    (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹))
  information_identDistrib : ∀ i,
    IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
      (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ
  score_memLp : MemLp
    (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ
  score_iIndep : iIndepFun
    (fun i ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω)) μ
  score_identDistrib : ∀ i,
    IdentDistrib
      (fun ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω))
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ μ
  score_mean_zero :
    meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0
  score_covariance_identity :
    covMat μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) =
      μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]
  information_nonsing : IsUnit
    (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det
  error_covariance_posSemidef : Sigma.PosSemidef
  linear_model : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j
  feasible_weight_substitution : TendstoInMeasure μ
    ((fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (surBetaEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
      fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromErrorCovStar
            (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
    atTop (fun _ => 0)

namespace SURGaussianLimitConditions

omit [Fintype n] [DecidableEq n] in
/-- Constructor for Hansen Theorem 11.4 conditions from conditional
homoskedasticity of the transformed SUR errors `Σ⁻¹e`.

Compared with `SURGaussianLimitConditions`, this constructor removes
the primitive `score_covariance_identity` field, and also gets the fixed
information integrability field from
`hweighted_hom.middle_integrable`. The exact remaining theorem-facing fields
are the iid/WLLN hypotheses for `X'Σ⁻¹X`, the iid CLT hypotheses and zero mean
for the weighted score `X'Σ⁻¹e`, nonsingularity of `E[X'Σ⁻¹X]`, positive
semidefiniteness of `Σ`, the linear model, observation measurability, and the
feasible `Σ̂⁻¹` substitution. -/
private theorem of_weighted_error_conditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hweighted_hom : SystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hinfo_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hinfo_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hscore_iIndep : iIndepFun
      (fun i ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω)) μ)
    (hscore_ident : ∀ i,
      IdentDistrib
        (fun ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω))
        (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hinfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β where
  x_aestronglyMeasurable := hX_meas
  y_aestronglyMeasurable := hY_meas
  information_integrable := hweighted_hom.middle_integrable
  information_independent := hinfo_indep
  information_identDistrib := hinfo_ident
  score_memLp := hscore_memLp
  score_iIndep := hscore_iIndep
  score_identDistrib := hscore_ident
  score_mean_zero := hscore_mean_zero
  score_covariance_identity :=
    weightedScore_covMat_eq_middle_of_weighted_error_conditionalHomoskedasticity
      (μ := μ) X e Sigma hscore_memLp hscore_mean_zero hweighted_hom
  information_nonsing := hinfo_unit
  error_covariance_posSemidef := hSigma_posSemidef
  linear_model := hmodel
  feasible_weight_substitution := hsub

omit [Fintype n] [DecidableEq n] in
/-- Constructor for Hansen Theorem 11.4 conditions from matrix-valued
conditional homoskedasticity of the transformed SUR errors `Σ⁻¹e`.

This is the literal-matrix counterpart of
`of_weighted_error_conditionalHomoskedasticity`; it removes the need for callers
to separately build the scalar transformed-error package. The feasible
`Σ̂⁻¹` substitution remains explicit because it is the rate-sensitive step in
the feasible SUR estimator. -/
private theorem of_weighted_error_matrix_conditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hinfo_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hinfo_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hscore_iIndep : iIndepFun
      (fun i ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω)) μ)
    (hscore_ident : ∀ i,
      IdentDistrib
        (fun ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω))
        (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hinfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_weighted_error_conditionalHomoskedasticity
    (μ := μ) (Z := Z) hX_meas hY_meas
    hweighted_hom.toSystemConditionalHomoskedasticity
    hinfo_indep hinfo_ident hscore_memLp hscore_iIndep hscore_ident
    hscore_mean_zero hinfo_unit hSigma_posSemidef hmodel hsub

omit [Fintype n] [DecidableEq n] in
/-- Constructor for Hansen Theorem 11.4 conditions from the raw matrix-valued
conditional homoskedasticity condition `(11.8)`.

Unlike `of_weighted_error_matrix_conditionalHomoskedasticity`, callers provide the literal
condition on `e`, not on the transformed error `Σ⁻¹e`. The transformed conditional
second-moment identity is derived internally from `Σ` positive definite. The remaining
transformed weighted-product integrability fields are kept explicit because they are side
conditions of the current formal package rather than consequences of the conditional moment
identity alone. -/
private theorem of_raw_error_matrix_conditionalHomoskedasticity
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef)
    (hweighted_robust : Integrable
      (fun ω => systemRobustMiddleTerm (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ)
    (hinfo_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hweighted_error : ∀ a b c d,
      Integrable
        (fun ω =>
          X 0 ω a c * X 0 ω b d *
            ((Sigma⁻¹ *ᵥ e 0 ω) a * (Sigma⁻¹ *ᵥ e 0 ω) b)) μ)
    (hweighted_sigma : ∀ a b c d,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma⁻¹ a b) μ)
    (hinfo_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hinfo_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hscore_iIndep : iIndepFun
      (fun i ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω)) μ)
    (hscore_ident : ∀ i,
      IdentDistrib
        (fun ω => systemScore (X i ω) (Sigma⁻¹ *ᵥ e i ω))
        (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hinfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_weighted_error_matrix_conditionalHomoskedasticity
    (μ := μ) (Z := Z) hX_meas hY_meas
    (hhom.inverseWeighted hSigma hweighted_robust hinfo_int
      hweighted_error hweighted_sigma)
    hinfo_indep hinfo_ident hscore_memLp hscore_iIndep hscore_ident
    hscore_mean_zero hinfo_unit hSigma.posSemidef hmodel hsub

omit [Fintype n] [DecidableEq n] in
/-- The fixed-`Σ⁻¹` score package derived from the Theorem 11.4 condition bundle. -/
private theorem scoreCLTConditions
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURGaussianLimitConditions μ X e Y Sigma β) :
    SURScoreCLTConditions μ X Sigma⁻¹ e
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]) :=
  SURScoreCLTConditions.of_weighted_score_moments
    (μ := μ) (X := X) (e := e) (W := Sigma⁻¹)
    h.information_integrable h.information_independent h.information_identDistrib
    h.score_memLp h.score_iIndep h.score_identDistrib h.score_mean_zero
    h.score_covariance_identity h.information_nonsing
    (Matrix.PosSemidef.inv h.error_covariance_posSemidef)

omit [Fintype n] [DecidableEq n] in
/-- Oracle fixed-error-covariance SUR CLT implied by the Theorem 11.4 condition bundle. -/
private theorem fixedErrorCovariance_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURGaussianLimitConditions μ X e Y Sigma β) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaFromErrorCovStar
            (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (surAsymptoticVariance
          (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))) :=
  surBetaFromErrorCovStar_tendstoInDistribution_of_weighted_score_moments
    (μ := μ) (X := X) (e := e) (Y := Y) Sigma β
    h.information_integrable h.information_independent h.information_identDistrib
    h.score_memLp h.score_iIndep h.score_identDistrib h.score_mean_zero
    h.score_covariance_identity h.information_nonsing h.error_covariance_posSemidef
    h.linear_model h.x_aestronglyMeasurable h.y_aestronglyMeasurable

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 for the named feasible SUR estimator, packaged as a
single theorem-facing endpoint. -/
theorem starObs
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURGaussianLimitConditions μ X e Y Sigma β) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (surAsymptoticVariance
          (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))) :=
  surBetaEstimatorStarObs_tendstoInDistribution_of_weighted_score_moments
    (μ := μ) (X := X) (e := e) (Y := Y) Sigma β
    h.information_integrable h.information_independent h.information_identDistrib
    h.score_memLp h.score_iIndep h.score_identDistrib h.score_mean_zero
    h.score_covariance_identity h.information_nonsing h.error_covariance_posSemidef
    h.linear_model h.feasible_weight_substitution
    h.x_aestronglyMeasurable h.y_aestronglyMeasurable

omit [Fintype n] [DecidableEq n] in
/-- Positive semidefiniteness of the SUR limit covariance in the Theorem 11.4
condition bundle. -/
private theorem asymptoticVariance_posSemidef
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURGaussianLimitConditions μ X e Y Sigma β) :
    (surAsymptoticVariance
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef := by
  have hM :
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).PosSemidef := by
    simpa [systemPopulationMiddle] using
      systemPopulationMiddle_posSemidef
        (μ := μ) (X := fun ω => X 0 ω) Sigma⁻¹
        h.information_integrable (Matrix.PosSemidef.inv h.error_covariance_posSemidef)
  simpa [surAsymptoticVariance] using Matrix.PosSemidef.inv hM

omit [Fintype n] [DecidableEq n] in
/-- Gaussian-limit interface form of Hansen Theorem 11.4 for the named feasible
SUR estimator. -/
private theorem starGaussianLimit
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURGaussianLimitConditions μ X e Y Sigma β) :
    GaussianLimit μ
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  gaussianLimit_of_tendstoInDistribution
    (fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (surBetaEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
    (surAsymptoticVariance
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))
    h.asymptoticVariance_posSemidef h.starObs

end SURGaussianLimitConditions

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
/-- Measurability of the feasible SUR information matrix from measurability of
`X` and the residual covariance estimator. -/
theorem surResidualCovarianceStarObs_information_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ)
    (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          ((systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)) μ :=
  systemHomoskedasticMiddle_estimated_aestronglyMeasurable
    (μ := μ) (X := X)
    (SigmaHat := fun t ω =>
      (systemSigmaHatStarObs
        (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
    hX_meas
    (fun t => surResidualCovarianceStarObs_inverse_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hSigmaHat_meas t)
    t

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Estimated-inverse-covariance route for feasible-SUR covariance consistency.

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

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Feasible SUR covariance consistency from inverse-covariance consistency and
bounded empirical design weights.

This discharges the raw middle-substitution premise of
`surCovariance_consistent_of_estimated_inverse_cov_substitution` from the more
primitive and reusable conditions `Σ̂⁻¹ ->p Σ⁻¹` and
`n⁻¹∑ XᵢaXᵢb = Oₚ(1)` coordinatewise. -/
theorem surCovariance_consistent_of_estimated_inverse_cov_bounded_weights
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
    (hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => SigmaInv))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) SigmaInv]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surVarianceEstimator
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) SigmaInv])) :=
  surCovariance_consistent_of_estimated_inverse_cov_substitution
    (μ := μ) (X := X) (SigmaInv := SigmaInv) (SigmaInvHat := SigmaInvHat)
    hint hindep hident hMhat_meas
    (SystemFeasible.middle_sub_zero_of_covariance_bounded_weights
      (μ := μ) (X := X) (SigmaHat := SigmaInvHat) (Sigma := SigmaInv)
      hSigmaInvHat hWeight)
    hM_unit

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] [Fintype m]
  [DecidableEq m] in
/-- Empirical SUR design weights are bounded in probability when their scalar
sample means satisfy the Chapter 11 WLLN primitive hypotheses. -/
theorem systemHomoskedasticMiddleWeight_bounded_of_wlln
    {X : ℕ → Ω → Matrix m k ℝ} (a b : m) (c d : k)
    (hint : Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => X i ω a c * X i ω b d)))
    (hident : ∀ i,
      IdentDistrib (fun ω => X i ω a c * X i ω b d)
        (fun ω => X 0 ω a c * X 0 ω b d) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        systemHomoskedasticMiddleWeight
          (fun i : Fin n => X i.val ω) a b c d) := by
  let W : ℕ → Ω → ℝ := fun i ω => X i ω a c * X i ω b d
  have hWLLN : TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω)
      atTop (fun _ => μ[W 0]) :=
    tendstoInMeasure_wlln W hint hindep hident
  have hWeight : TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddleWeight
          (fun i : Fin n => X i.val ω) a b c d)
      atTop (fun _ => μ[W 0]) := by
    refine hWLLN.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have hsum :
        (∑ i : Fin n, X i.val ω a c * X i.val ω b d) =
          ∑ i ∈ Finset.range n, X i ω a c * X i ω b d :=
      Fin.sum_univ_eq_sum_range (fun i => X i ω a c * X i ω b d) n
    simp [systemHomoskedasticMiddleWeight, W, Fintype.card_fin, hsum]
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Feasible SUR covariance consistency from inverse-covariance consistency and
scalar WLLN primitives for the empirical design weights. -/
private theorem surCovariance_consistent_of_estimated_inverse_cov_weight_wlln
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
    (hSigmaInvHat : TendstoInMeasure μ SigmaInvHat atTop (fun _ => SigmaInv))
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hWeight_indep : ∀ a b : m, ∀ c d : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a c * X i ω b d)))
    (hWeight_ident : ∀ a b : m, ∀ c d : k, ∀ i,
      IdentDistrib (fun ω => X i ω a c * X i ω b d)
        (fun ω => X 0 ω a c * X 0 ω b d) μ μ)
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) SigmaInv]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surVarianceEstimator
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) (SigmaInvHat t ω)))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) SigmaInv])) :=
  surCovariance_consistent_of_estimated_inverse_cov_bounded_weights
    (μ := μ) (X := X) (SigmaInv := SigmaInv) (SigmaInvHat := SigmaInvHat)
    hint hindep hident hMhat_meas hSigmaInvHat
    (fun a b c d =>
      systemHomoskedasticMiddleWeight_bounded_of_wlln
        (μ := μ) (X := X) a b c d
        (hWeight_int a b c d) (hWeight_indep a b c d)
        (hWeight_ident a b c d))
    hM_unit

/-- Feasible-SUR covariance-consistency wrapper for the actual residual covariance.

This specializes the estimated-inverse covariance route to
`Σ̂ = systemSigmaHatStarObs X Y`. The remaining assumption `hsub` is the
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
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)) μ)
    (hsub : TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹) -
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)
      atTop (fun _ => 0))
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surVarianceEstimator
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovariance_consistent_of_estimated_inverse_cov_substitution
    (μ := μ) (X := X) (SigmaInv := Sigma⁻¹)
    (SigmaInvHat := fun t ω =>
      (systemSigmaHatStarObs
        (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
    hint hindep hident hMhat_meas hsub hM_unit

/-- Feasible-SUR covariance-consistency wrapper for the actual residual covariance,
using inverse residual-covariance consistency plus bounded empirical design
weights to derive the information-matrix perturbation. -/
theorem surCovariance_consistent_of_residualCovarianceStarObs_bounded_weights
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
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)) μ)
    (hSigmaInvHat : TendstoInMeasure μ
      (fun t ω =>
        (systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
      atTop (fun _ => Sigma⁻¹))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surVarianceEstimator
          (systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovariance_consistent_of_estimated_inverse_cov_bounded_weights
    (μ := μ) (X := X) (SigmaInv := Sigma⁻¹)
    (SigmaInvHat := fun t ω =>
      (systemSigmaHatStarObs
        (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
    hint hindep hident hMhat_meas hSigmaInvHat hWeight hM_unit

/-- Covariance-consistency wrapper for the named feasible SUR covariance estimator
`surCovarianceEstimatorStarObs`. This is a notational specialization of
`surCovariance_consistent_of_residualCovarianceStarObs_substitution`. -/
private theorem surCovarianceEstimatorStarObs_consistent_of_substitution
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
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)) μ)
    (hsub : TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹) -
          systemHomoskedasticMiddle (fun i : Fin t => X i.val ω) Sigma⁻¹)
      atTop (fun _ => 0))
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) := by
  simpa [surCovarianceEstimatorStarObs] using
    surCovariance_consistent_of_residualCovarianceStarObs_substitution
      (μ := μ) (X := X) (Y := Y) Sigma hint hindep hident
      hMhat_meas hsub hM_unit

/-- Hansen-facing covariance consistency for the named feasible SUR estimator,
using the bounded-weight perturbation route. -/
theorem surCovarianceEstimatorStarObs_consistent_of_bounded_weights
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
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)) μ)
    (hSigmaInvHat : TendstoInMeasure μ
      (fun t ω =>
        (systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
      atTop (fun _ => Sigma⁻¹))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) := by
  simpa [surCovarianceEstimatorStarObs] using
    surCovariance_consistent_of_residualCovarianceStarObs_bounded_weights
      (μ := μ) (X := X) (Y := Y) Sigma hint hindep hident
      hMhat_meas hSigmaInvHat hWeight hM_unit

/-- Hansen-facing covariance consistency for the named feasible SUR estimator
from primitive residual-covariance consistency.

This version removes the inverse-convergence premise from
`surCovarianceEstimatorStarObs_consistent_of_bounded_weights`: the convergence
`Σ̂ ->p Σ`, together with nonsingularity of `Σ`, supplies
`Σ̂⁻¹ ->p Σ⁻¹` by inverse CMT. -/
theorem surCovarianceEstimatorStarObs_consistent_of_residualCovariance_bounded_weights
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
            ((systemSigmaHatStarObs
              (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)) μ)
    (hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det)
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d))
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovarianceEstimatorStarObs_consistent_of_bounded_weights
    (μ := μ) (X := X) (Y := Y) Sigma hint hindep hident hMhat_meas
    (surResidualCovarianceStarObs_inverse_tendstoInMeasure
      (μ := μ) (X := X) (Y := Y) (Sigma := Sigma)
      hSigmaHat_meas hSigmaHat hSigma_unit)
    hWeight hM_unit

/-- Hansen-facing covariance consistency for the named feasible SUR estimator
from residual-covariance consistency and scalar WLLN primitives for the
empirical design weights. -/
theorem surCovarianceEstimatorStarObs_consistent_of_residualCovariance_weight_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ)
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hSigmaHat_meas : ∀ t,
      AEStronglyMeasurable
        (fun ω =>
          systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det)
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hWeight_indep : ∀ a b : m, ∀ c d : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a c * X i ω b d)))
    (hWeight_ident : ∀ a b : m, ∀ c d : k, ∀ i,
      IdentDistrib (fun ω => X i ω a c * X i ω b d)
        (fun ω => X 0 ω a c * X 0 ω b d) μ μ)
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovarianceEstimatorStarObs_consistent_of_residualCovariance_bounded_weights
    (μ := μ) (X := X) (Y := Y) Sigma hint hindep hident
    (surResidualCovarianceStarObs_information_aestronglyMeasurable
      (μ := μ) (X := X) (Y := Y) hX_meas hSigmaHat_meas)
    hSigmaHat_meas hSigmaHat hSigma_unit
    (fun a b c d =>
      systemHomoskedasticMiddleWeight_bounded_of_wlln
        (μ := μ) (X := X) a b c d
        (hWeight_int a b c d) (hWeight_indep a b c d)
        (hWeight_ident a b c d))
    hM_unit

/-- Hansen-facing covariance consistency for the named feasible SUR estimator
from residual-covariance consistency, observation-level measurability, and
scalar WLLN primitives for the empirical design weights.

Compared with `surCovarianceEstimatorStarObs_consistent_of_residualCovariance_weight_wlln`,
this wrapper derives measurability of the actual residual covariance
`Σ̂ = n⁻¹∑ êᵢêᵢ'` from measurability of `X` and `Y`. -/
private theorem surCovarianceEstimatorStarObs_consistent_of_observation_measurable_weight_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (Sigma : Matrix m m ℝ)
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹)))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det)
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hWeight_indep : ∀ a b : m, ∀ c d : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a c * X i ω b d)))
    (hWeight_ident : ∀ a b : m, ∀ c d : k, ∀ i,
      IdentDistrib (fun ω => X i ω a c * X i ω b d)
        (fun ω => X 0 ω a c * X 0 ω b d) μ μ)
    (hM_unit : IsUnit (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovarianceEstimatorStarObs_consistent_of_residualCovariance_weight_wlln
    (μ := μ) (X := X) (Y := Y) Sigma hint hindep hident hX_meas
    (fun t =>
      surResidualCovarianceStarObs_aestronglyMeasurable
        (μ := μ) (X := X) (Y := Y) hX_meas hY_meas t)
    hSigmaHat hSigma_unit hWeight_int hWeight_indep hWeight_ident hM_unit

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Residual-covariance consistency from a true-error covariance WLLN plus a
feasible-residual covariance substitution.

This is the sharp perturbation step for feasible-SUR covariance consistency:
`Σ̂(ê) - Σ̂(e) = oₚ(1)` transfers the true-error covariance limit to the
actual feasible SUR residual covariance. -/
theorem surResidualCovarianceStarObs_tendstoInMeasure_of_true_error_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (hideal : TendstoInMeasure μ
      (fun t ω => systemSigmaHat (fun i : Fin t => e i.val ω))
      atTop (fun _ => Sigma))
    (hsub : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) -
          systemSigmaHat (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0)) :
  TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma) :=
  systemSigmaHatStarObs_tendstoInMeasure_of_true_error_substitution hideal hsub


omit [Fintype n] [DecidableEq n] in
/-- Primitive package for feasible-SUR covariance consistency.

The target theorem is covariance consistency of the feasible SUR covariance
estimator
`(n⁻¹∑ Xᵢ'Σ̂⁻¹Xᵢ)⁻¹`, where `Σ̂ = n⁻¹∑ êᵢêᵢ'`.

The package keeps the remaining stochastic primitives explicit:
* `residual_covariance_tendsto` is the residual covariance consistency step
  `Σ̂ ->p Σ`;
* `information_*` are the fixed-`Σ⁻¹` WLLN hypotheses for
  `n⁻¹∑ Xᵢ'Σ⁻¹Xᵢ`;
* `design_weight_*` are scalar WLLN hypotheses used only to justify replacing
  `Σ⁻¹` by `Σ̂⁻¹` inside Hansen's information matrix. -/
structure SURCovarianceEstimatorConsistencyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (Y : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ) : Prop where
  x_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (X i) μ
  y_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (Y i) μ
  residual_covariance_tendsto : TendstoInMeasure μ
    (fun t ω =>
      systemSigmaHatStarObs
        (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
    atTop (fun _ => Sigma)
  error_covariance_nonsing : IsUnit Sigma.det
  information_integrable : Integrable
    (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ
  information_independent : Pairwise ((· ⟂ᵢ[μ] ·) on
    (fun i ω => systemMiddleTerm (X i ω) Sigma⁻¹))
  information_identDistrib : ∀ i,
    IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma⁻¹)
      (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ μ
  design_weight_integrable : ∀ a b : m, ∀ c d : k,
    Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ
  design_weight_independent : ∀ a b : m, ∀ c d : k,
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => X i ω a c * X i ω b d))
  design_weight_identDistrib : ∀ a b : m, ∀ c d : k, ∀ i,
    IdentDistrib (fun ω => X i ω a c * X i ω b d)
      (fun ω => X 0 ω a c * X 0 ω b d) μ μ
  information_nonsing : IsUnit
    (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det

namespace SURCovarianceEstimatorConsistencyConditions

omit [Fintype n] [DecidableEq n] in
/-- The actual feasible SUR residual covariance is measurable from the
observation-level measurability fields. -/
theorem residualCovariance_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ :=
  surResidualCovarianceStarObs_aestronglyMeasurable
    (μ := μ) (X := X) (Y := Y)
    h.x_aestronglyMeasurable h.y_aestronglyMeasurable t

omit [Fintype n] [DecidableEq n] in
/-- Hansen's `Σ̂ ->p Σ` primitive gives `Σ̂⁻¹ ->p Σ⁻¹` by the existing
matrix inverse CMT. -/
theorem residualCovariance_inverse_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma) :
    TendstoInMeasure μ
      (fun t ω =>
        (systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
      atTop (fun _ => Sigma⁻¹) :=
  surResidualCovarianceStarObs_inverse_tendstoInMeasure
    (μ := μ) (X := X) (Y := Y) (Sigma := Sigma)
    (fun t => h.residualCovariance_aestronglyMeasurable t)
    h.residual_covariance_tendsto h.error_covariance_nonsing

omit [Fintype n] [DecidableEq n] in
/-- Measurability of Hansen's feasible SUR information matrix
`n⁻¹∑ Xᵢ'Σ̂⁻¹Xᵢ`. -/
theorem information_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          ((systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)) μ :=
  surResidualCovarianceStarObs_information_aestronglyMeasurable
    (μ := μ) (X := X) (Y := Y)
    h.x_aestronglyMeasurable
    (fun t => h.residualCovariance_aestronglyMeasurable t) t

omit [Fintype n] [DecidableEq n] in
/-- Feasible-SUR information-matrix consistency:
`n⁻¹∑ Xᵢ'Σ̂⁻¹Xᵢ ->p E[Xᵢ'Σ⁻¹Xᵢ]`. -/
theorem information_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma) :
    TendstoInMeasure μ
      (fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          ((systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹))
      atTop
      (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]) :=
  SystemFeasible.middle_of_covariance_bounded_weights
    (μ := μ) (X := X)
    (SigmaHat := fun t ω =>
      (systemSigmaHatStarObs
        (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹)
    (Sigma := Sigma⁻¹)
    (systemHomoskedasticMiddle_fixed_tendstoInMeasure
      (μ := μ) (X := X) Sigma⁻¹
      h.information_integrable h.information_independent
      h.information_identDistrib)
    h.residualCovariance_inverse_tendstoInMeasure
    (fun a b c d =>
      systemHomoskedasticMiddleWeight_bounded_of_wlln
        (μ := μ) (X := X) a b c d
        (h.design_weight_integrable a b c d)
        (h.design_weight_independent a b c d)
        (h.design_weight_identDistrib a b c d))

omit [Fintype n] [DecidableEq n] in
/-- Measurability of Hansen's named feasible SUR covariance estimator
`(n⁻¹∑ Xᵢ'Σ̂⁻¹Xᵢ)⁻¹`. -/
theorem covarianceEstimator_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma) (t : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) μ := by
  simpa [surCovarianceEstimatorStarObs, surVarianceEstimator] using
    aestronglyMeasurable_matrix_inv (h.information_aestronglyMeasurable t)

omit [Fintype n] [DecidableEq n] in
/-- Direct convergence statement for the named feasible SUR
covariance estimator. -/
theorem covarianceEstimator_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma) :
    TendstoInMeasure μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop
      (fun _ =>
        surAsymptoticVariance
          (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) := by
  simpa [surCovarianceEstimatorStarObs] using
    surVarianceEstimator_tendstoInMeasure
      (μ := μ)
      (Mhat := fun t ω =>
        systemHomoskedasticMiddle (fun i : Fin t => X i.val ω)
          ((systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))⁻¹))
      (M := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])
      (fun t => h.information_aestronglyMeasurable t)
      h.information_tendstoInMeasure h.information_nonsing

omit [Fintype n] [DecidableEq n] in
/-- Covariance-estimator interface for the named
feasible SUR covariance estimator. -/
theorem covarianceEstimator_consistent
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  covarianceEstimatorConsistent_of_tendstoInMeasure
    (fun t ω =>
      surCovarianceEstimatorStarObs
        (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
    (surAsymptoticVariance
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))
    (fun t => h.covarianceEstimator_aestronglyMeasurable t)
    h.covarianceEstimator_tendstoInMeasure

end SURCovarianceEstimatorConsistencyConditions

omit [Fintype n] [DecidableEq n] in
/-- Feasible SUR beta substitution from the Chapter 11 covariance-consistency
package and scalar score-weight tightness.

This is the main constructor-style bridge for Hansen Theorem 11.4's remaining
feasible-weight step: `SURCovarianceEstimatorConsistencyConditions` supplies
`Σ̂ ->p Σ`, nonsingularity, observation measurability, and the scalar design
WLLNs; the only stochastic primitive left here is the coordinatewise
`Oₚ(1)` bound for `√n n⁻¹∑ X_iaj e_ib`. -/
theorem surBetaEstimatorStarObs_feasible_weight_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {M : Matrix k k ℝ} {β : k → ℝ}
    (hscore : SURScoreCLTConditions μ X Sigma⁻¹ e M)
    (hcov : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hScoreWeight : ∀ a b : m, ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          Real.sqrt (t : ℝ) *
            surWeightedScoreScalarWeight
              (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j)) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0) := by
  have hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun t ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin t => X i.val ω) a b c d) :=
    fun a b c d =>
      systemHomoskedasticMiddleWeight_bounded_of_wlln
        (μ := μ) (X := X) a b c d
        (hcov.design_weight_integrable a b c d)
        (hcov.design_weight_independent a b c d)
        (hcov.design_weight_identDistrib a b c d)
  exact
    surBetaEstimatorStarObs_substitution_of_residualCovariance_bounded_score_weights
      (μ := μ) (X := X) (e := e) (Y := Y) Sigma hscore β hmodel
      hcov.x_aestronglyMeasurable he_meas hcov.y_aestronglyMeasurable
      hcov.residual_covariance_tendsto hcov.error_covariance_nonsing
      hWeight hScoreWeight

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Measurability of the one-observation SUR information contribution as a
function of the per-observation system design. -/
private theorem measurable_systemMiddleTerm_const (W : Matrix m m ℝ) :
    Measurable (fun A : Matrix m k ℝ => systemMiddleTerm A W) := by
  have hLeft : Continuous (fun A : Matrix m k ℝ => Aᵀ * W) :=
    Continuous.matrix_mul continuous_id.matrix_transpose continuous_const
  simpa [systemMiddleTerm, Matrix.mul_assoc] using
    (Continuous.matrix_mul hLeft continuous_id).measurable

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Measurability of a one-observation weighted SUR score as a function of the
joint row `(Xᵢ, eᵢ)`. -/
private theorem measurable_weightedSystemScore_row_const (W : Matrix m m ℝ) :
    Measurable
      (fun p : Matrix m k ℝ × (m → ℝ) => systemScore p.1 (W *ᵥ p.2)) := by
  have hX : Continuous (fun p : Matrix m k ℝ × (m → ℝ) => p.1) := continuous_fst
  have hXT : Continuous (fun p : Matrix m k ℝ × (m → ℝ) => p.1ᵀ) :=
    hX.matrix_transpose
  have hWe : Continuous (fun p : Matrix m k ℝ × (m → ℝ) => W *ᵥ p.2) :=
    Continuous.matrix_mulVec continuous_const continuous_snd
  simpa [systemScore] using (Continuous.matrix_mulVec hXT hWe).measurable

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Measurability of a scalar design-weight contribution as a function of the
per-observation system design. -/
private theorem measurable_systemHomoskedasticMiddleWeightTerm
    (a b : m) (c d : k) :
    Measurable (fun A : Matrix m k ℝ => A a c * A b d) := by
  have ha : Continuous (fun A : Matrix m k ℝ => A a c) :=
    (continuous_apply c).comp (continuous_apply a)
  have hb : Continuous (fun A : Matrix m k ℝ => A b d) :=
    (continuous_apply d).comp (continuous_apply b)
  exact (ha.mul hb).measurable

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Observation-level iid design implies pairwise independence of fixed SUR
information contributions `Xᵢ' W Xᵢ`. -/
theorem systemMiddleTerm_independent_of_iIndep_design
    {X : ℕ → Ω → Matrix m k ℝ} (W : Matrix m m ℝ)
    (hX_iIndep : iIndepFun X μ) :
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) W)) := by
  have hmid : iIndepFun (fun i ω => systemMiddleTerm (X i ω) W) μ := by
    simpa [Function.comp_def] using
      hX_iIndep.comp (fun _ A => systemMiddleTerm A W)
        (fun _ => measurable_systemMiddleTerm_const (k := k) W)
  intro i j hij
  exact hmid.indepFun hij

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Observation-level identical distribution of the system design implies
identical distribution of fixed SUR information contributions `Xᵢ' W Xᵢ`. -/
theorem systemMiddleTerm_identDistrib_of_identDistrib_design
    {X : ℕ → Ω → Matrix m k ℝ} (W : Matrix m m ℝ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (i : ℕ) :
    IdentDistrib (fun ω => systemMiddleTerm (X i ω) W)
      (fun ω => systemMiddleTerm (X 0 ω) W) μ μ := by
  simpa [Function.comp_def] using
    (hX_ident i).comp (measurable_systemMiddleTerm_const (k := k) W)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Joint row iid implies pairwise independence of fixed SUR information
contributions `Xᵢ' W Xᵢ`. -/
theorem systemMiddleTerm_independent_of_iIndep_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ} (W : Matrix m m ℝ)
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ) :
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) W)) := by
  have hmid : iIndepFun (fun i ω => systemMiddleTerm (X i ω) W) μ := by
    simpa [Function.comp_def] using
      hrow_iIndep.comp (fun _ p => systemMiddleTerm p.1 W)
        (fun _ => (measurable_systemMiddleTerm_const (k := k) W).comp measurable_fst)
  intro i j hij
  exact hmid.indepFun hij

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Joint row identical distribution implies identical distribution of fixed
SUR information contributions `Xᵢ' W Xᵢ`. -/
theorem systemMiddleTerm_identDistrib_of_identDistrib_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ} (W : Matrix m m ℝ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (i : ℕ) :
    IdentDistrib (fun ω => systemMiddleTerm (X i ω) W)
      (fun ω => systemMiddleTerm (X 0 ω) W) μ μ := by
  simpa [Function.comp_def] using
    (hrow_ident i).comp
      ((measurable_systemMiddleTerm_const (k := k) W).comp measurable_fst)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Joint row iid implies iid weighted SUR scores `Xᵢ' W eᵢ`. -/
theorem weightedSystemScore_iIndep_of_iIndep_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ} (W : Matrix m m ℝ)
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ) :
    iIndepFun (fun i ω => systemScore (X i ω) (W *ᵥ e i ω)) μ := by
  simpa [Function.comp_def] using
    hrow_iIndep.comp (fun _ p => systemScore p.1 (W *ᵥ p.2))
      (fun _ => measurable_weightedSystemScore_row_const (k := k) W)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Joint row identical distribution implies identical distribution of weighted
SUR scores `Xᵢ' W eᵢ`. -/
theorem weightedSystemScore_identDistrib_of_identDistrib_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ} (W : Matrix m m ℝ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (i : ℕ) :
    IdentDistrib (fun ω => systemScore (X i ω) (W *ᵥ e i ω))
      (fun ω => systemScore (X 0 ω) (W *ᵥ e 0 ω)) μ μ := by
  simpa [Function.comp_def] using
    (hrow_ident i).comp (measurable_weightedSystemScore_row_const (k := k) W)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Measurability of the scalar cross product `X_iaj e_ib` as a function of a
joint observation row. -/
private theorem measurable_surWeightedScoreScalar_row (a b : m) (j : k) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) => row.1 a j * row.2 b) := by
  have hfst : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1) :=
    continuous_fst
  have hsnd : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.2) :=
    continuous_snd
  have hXa : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1 a) :=
    (continuous_apply a).comp hfst
  have hXaj : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1 a j) :=
    (continuous_apply j).comp hXa
  have heb : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.2 b) :=
    (continuous_apply b).comp hsnd
  exact (hXaj.mul heb).measurable

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Joint row iid implies iid scalar cross products `X_iaj e_ib`. -/
private theorem surWeightedScoreScalar_iIndep_of_iIndep_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (a b : m) (j : k) :
    iIndepFun (fun i ω => X i ω a j * e i ω b) μ := by
  simpa [Function.comp_def] using
    hrow_iIndep.comp
      (fun _ (row : Matrix m k ℝ × (m → ℝ)) => row.1 a j * row.2 b)
      (fun _ => measurable_surWeightedScoreScalar_row (k := k) a b j)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Joint row identical distribution implies identical distribution of scalar
cross products `X_iaj e_ib`. -/
private theorem surWeightedScoreScalar_identDistrib_of_identDistrib_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (a b : m) (j : k) (i : ℕ) :
    IdentDistrib (fun ω => X i ω a j * e i ω b)
      (fun ω => X 0 ω a j * e 0 ω b) μ μ := by
  simpa [Function.comp_def] using
    (hrow_ident i).comp
      (measurable_surWeightedScoreScalar_row (k := k) a b j)

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- Scalar cross-score tightness from joint-row iid, raw conditional
exogeneity, and coordinatewise finite second moments.

This is the Hansen Theorem 11.4 helper that turns the remaining
`√n n⁻¹∑ X_iaj e_ib = Oₚ(1)` primitive into ordinary iid scalar-CLT inputs. -/
theorem surWeightedScoreScalarWeight_boundedInProbability_of_iid_row_condMeanZero
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hexog : SystemConditionalMeanZero μ Z X e)
    (a b : m) (j : k)
    (hmem : MemLp (fun ω => X 0 ω a j * e 0 ω b) 2 μ) :
    BoundedInProbability μ
      (fun t ω =>
        Real.sqrt (t : ℝ) *
          surWeightedScoreScalarWeight
            (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j) := by
  have hmean : μ[fun ω => X 0 ω a j * e 0 ω b] = 0 :=
    hexog.scalar_cross_mean_zero a b j (hmem.integrable (by norm_num))
  exact
    surWeightedScoreScalarWeight_boundedInProbability_of_iid_clt
      (μ := μ) (X := X) (e := e) a b j hmem
      (surWeightedScoreScalar_iIndep_of_iIndep_row
        (μ := μ) (X := X) (e := e) hrow_iIndep a b j)
      (fun i =>
        surWeightedScoreScalar_identDistrib_of_identDistrib_row
          (μ := μ) (X := X) (e := e) hrow_ident a b j i)
      hmean

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Observation-level iid design implies pairwise independence of the scalar
empirical design-weight contributions used by feasible SUR. -/
theorem systemHomoskedasticMiddleWeight_independent_of_iIndep_design
    {X : ℕ → Ω → Matrix m k ℝ}
    (hX_iIndep : iIndepFun X μ) (a b : m) (c d : k) :
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => X i ω a c * X i ω b d)) := by
  have hweight : iIndepFun (fun i ω => X i ω a c * X i ω b d) μ := by
    simpa [Function.comp_def] using
      hX_iIndep.comp (fun _ A => A a c * A b d)
        (fun _ => measurable_systemHomoskedasticMiddleWeightTerm (k := k) a b c d)
  intro i j hij
  exact hweight.indepFun hij

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Observation-level identical distribution of the system design implies
identical distribution of the scalar empirical design-weight contributions used
by feasible SUR. -/
theorem systemHomoskedasticMiddleWeight_identDistrib_of_identDistrib_design
    {X : ℕ → Ω → Matrix m k ℝ}
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (a b : m) (c d : k) (i : ℕ) :
    IdentDistrib (fun ω => X i ω a c * X i ω b d)
      (fun ω => X 0 ω a c * X 0 ω b d) μ μ := by
  simpa [Function.comp_def] using
    (hX_ident i).comp
      (measurable_systemHomoskedasticMiddleWeightTerm (k := k) a b c d)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem design_iIndep_of_iIndep_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ) :
    iIndepFun X μ := by
  simpa [Function.comp_def] using
    hrow_iIndep.comp (fun _ (row : Matrix m k ℝ × (m → ℝ)) => row.1)
      (fun _ => measurable_fst)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem design_identDistrib_of_identDistrib_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (i : ℕ) :
    IdentDistrib (X i) (X 0) μ μ := by
  simpa [Function.comp_def] using (hrow_ident i).comp measurable_fst

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem measurable_errorOuter_row :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      Matrix.vecMulVec row.2 row.2) :=
  (Continuous.matrix_vecMulVec continuous_snd continuous_snd).measurable

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem errorOuter_independent_of_iIndep_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ) :
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))) := by
  have houter : iIndepFun
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω)) μ := by
    simpa [Function.comp_def] using
      hrow_iIndep.comp
        (fun _ (row : Matrix m k ℝ × (m → ℝ)) =>
          Matrix.vecMulVec row.2 row.2)
        (fun _ => measurable_errorOuter_row (m := m))
  intro i j hij
  exact houter.indepFun hij

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem errorOuter_identDistrib_of_identDistrib_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (i : ℕ) :
    IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
      (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ := by
  simpa [Function.comp_def] using
    (hrow_ident i).comp (measurable_errorOuter_row (m := m))

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem measurable_residualCrossWeight_row (a b : m) (l : k) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      row.2 a * row.1 b l + row.1 a l * row.2 b) := by
  have hfst : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1) :=
    continuous_fst
  have hsnd : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.2) :=
    continuous_snd
  have hea : Measurable (fun row : Matrix m k ℝ × (m → ℝ) => row.2 a) :=
    ((continuous_apply a).comp hsnd).measurable
  have heb : Measurable (fun row : Matrix m k ℝ × (m → ℝ) => row.2 b) :=
    ((continuous_apply b).comp hsnd).measurable
  have hXb : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1 b) :=
    (continuous_apply b).comp hfst
  have hXa : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1 a) :=
    (continuous_apply a).comp hfst
  have hXbl : Measurable (fun row : Matrix m k ℝ × (m → ℝ) => row.1 b l) :=
    ((continuous_apply l).comp hXb).measurable
  have hXal : Measurable (fun row : Matrix m k ℝ × (m → ℝ) => row.1 a l) :=
    ((continuous_apply l).comp hXa).measurable
  exact (hea.mul hXbl).add (hXal.mul heb)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem residualCrossWeight_independent_of_iIndep_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (a b : m) (l : k) :
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => e i ω a * X i ω b l + X i ω a l * e i ω b)) := by
  let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
    row.2 a * row.1 b l + row.1 a l * row.2 b
  have hcross : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
    simpa [f, Function.comp_def] using
      hrow_iIndep.comp (fun _ => f)
        (fun _ => measurable_residualCrossWeight_row (k := k) a b l)
  intro i j hij
  exact hcross.indepFun hij

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem residualCrossWeight_identDistrib_of_identDistrib_row
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (a b : m) (l : k) (i : ℕ) :
    IdentDistrib
      (fun ω => e i ω a * X i ω b l + X i ω a l * e i ω b)
      (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ μ := by
  let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
    row.2 a * row.1 b l + row.1 a l * row.2 b
  have hi := (hrow_ident i).comp
    (measurable_residualCrossWeight_row (k := k) a b l)
  simpa [f, Function.comp_def] using hi

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq k] [DecidableEq m] in
private theorem errorCoordinate_aestronglyMeasurable_of_linear_model
    {X0 : Ω → Matrix m k ℝ} {e0 Y0 : Ω → m → ℝ} {β : k → ℝ}
    (hX : AEStronglyMeasurable X0 μ) (hY : AEStronglyMeasurable Y0 μ)
    (hmodel : ∀ ω j, Y0 ω j = (X0 ω j) ⬝ᵥ β + e0 ω j) (a : m) :
    AEStronglyMeasurable (fun ω => e0 ω a) μ := by
  have hYc : AEStronglyMeasurable (fun ω => Y0 ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable hY
  have hdot : AEStronglyMeasurable (fun ω => (X0 ω a) ⬝ᵥ β) μ := by
    classical
    have hXa : AEStronglyMeasurable (fun ω => X0 ω a) μ :=
      (continuous_apply a).comp_aestronglyMeasurable hX
    simpa [dotProduct] using
      Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun j _ =>
        (((continuous_apply j).comp_aestronglyMeasurable hXa).mul_const (β j)))
  refine (hYc.sub hdot).congr (ae_of_all μ (fun ω => ?_))
  calc
    Y0 ω a - (X0 ω a) ⬝ᵥ β =
        ((X0 ω a) ⬝ᵥ β + e0 ω a) - (X0 ω a) ⬝ᵥ β := by
          rw [hmodel ω a]
    _ = e0 ω a := by ring

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Coordinate measurability of the fixed-weight SUR score under the system
linear model. -/
private theorem weightedSystemScore_coordinate_aestronglyMeasurable_of_linear_model
    {X0 : Ω → Matrix m k ℝ} {e0 Y0 : Ω → m → ℝ} {β : k → ℝ}
    (W : Matrix m m ℝ)
    (hX : AEStronglyMeasurable X0 μ) (hY : AEStronglyMeasurable Y0 μ)
    (hmodel : ∀ ω j, Y0 ω j = (X0 ω j) ⬝ᵥ β + e0 ω j) (c : k) :
    AEStronglyMeasurable (fun ω => systemScore (X0 ω) (W *ᵥ e0 ω) c) μ := by
  classical
  have he_meas : ∀ a : m, AEStronglyMeasurable (fun ω => e0 ω a) μ :=
    fun a =>
      errorCoordinate_aestronglyMeasurable_of_linear_model
        (μ := μ) hX hY hmodel a
  have hterm : ∀ a : m,
      AEStronglyMeasurable
        (fun ω => X0 ω a c * (∑ b : m, W a b * e0 ω b)) μ := by
    intro a
    have hXac : AEStronglyMeasurable (fun ω => X0 ω a c) μ :=
      (continuous_apply c).comp_aestronglyMeasurable
        ((continuous_apply a).comp_aestronglyMeasurable hX)
    have hWe : AEStronglyMeasurable
        (fun ω => ∑ b : m, W a b * e0 ω b) μ := by
      exact Finset.aestronglyMeasurable_fun_sum Finset.univ
        (fun b _ => (he_meas b).const_mul (W a b))
    exact hXac.mul hWe
  have hsum : AEStronglyMeasurable
      (fun ω => ∑ a : m, X0 ω a c * (∑ b : m, W a b * e0 ω b)) μ :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun a _ => hterm a)
  refine hsum.congr (ae_of_all μ (fun ω => ?_))
  simp [systemScore, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Integrability of the score outer-product matrix gives a finite second
moment for the corresponding system score. -/
theorem systemScore_memLp_two_of_robustMiddleTerm_integrable
    {X0 : Ω → Matrix m k ℝ} {u0 : Ω → m → ℝ}
    (hscore_meas : ∀ c : k,
      AEStronglyMeasurable (fun ω => systemScore (X0 ω) (u0 ω) c) μ)
    (hRobust : Integrable (fun ω => systemRobustMiddleTerm (X0 ω) (u0 ω)) μ) :
    MemLp (fun ω => systemScore (X0 ω) (u0 ω)) 2 μ := by
  classical
  refine MemLp.of_eval ?_
  intro c
  have hdiag : Integrable
      (fun ω => systemRobustMiddleTerm (X0 ω) (u0 ω) c c) μ :=
    Integrable.eval (Integrable.eval hRobust c) c
  have hsq : Integrable (fun ω => (systemScore (X0 ω) (u0 ω) c) ^ 2) μ := by
    simpa [systemRobustMiddleTerm_eq_vecMulVec_score, Matrix.vecMulVec_apply, pow_two]
      using hdiag
  exact (memLp_two_iff_integrable_sq (hscore_meas c)).2 hsq

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Weighted-score finite second moment from the transformed score-middle
integrability supplied by a matrix homoskedasticity package. -/
theorem weightedSystemScore_memLp_two_of_linear_model_robust_integrable
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (W : Matrix m m ℝ)
    (hX_meas : AEStronglyMeasurable (X 0) μ)
    (hY_meas : AEStronglyMeasurable (Y 0) μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hRobust : Integrable
      (fun ω => systemRobustMiddleTerm (X 0 ω) (W *ᵥ e 0 ω)) μ) :
    MemLp (fun ω => systemScore (X 0 ω) (W *ᵥ e 0 ω)) 2 μ :=
  systemScore_memLp_two_of_robustMiddleTerm_integrable
    (μ := μ) (X0 := X 0) (u0 := fun ω => W *ᵥ e 0 ω)
    (fun c =>
      weightedSystemScore_coordinate_aestronglyMeasurable_of_linear_model
        (μ := μ) (X0 := X 0) (e0 := e 0) (Y0 := Y 0)
        (β := β) W hX_meas hY_meas (fun ω j => hmodel 0 ω j) c)
    hRobust

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem errorCoordinate_memLp_two_of_outer_integrable
    {e0 : Ω → m → ℝ}
    (he_meas : ∀ a : m, AEStronglyMeasurable (fun ω => e0 ω a) μ)
    (hOuter : Integrable (fun ω => Matrix.vecMulVec (e0 ω) (e0 ω)) μ)
    (a : m) :
    MemLp (fun ω => e0 ω a) 2 μ := by
  have hdiag : Integrable (fun ω => Matrix.vecMulVec (e0 ω) (e0 ω) a a) μ :=
    Integrable.eval (Integrable.eval hOuter a) a
  have hsq : Integrable (fun ω => (e0 ω a) ^ 2) μ := by
    simpa [Matrix.vecMulVec_apply, pow_two] using hdiag
  exact (memLp_two_iff_integrable_sq (he_meas a)).2 hsq

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem residualCrossWeight_integrable_of_model_memLp
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (hX_meas : AEStronglyMeasurable (X 0) μ)
    (hY_meas : AEStronglyMeasurable (Y 0) μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_memLp : MemLp (X 0) 2 μ)
    (hOuter : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (a b : m) (l : k) :
    Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ := by
  have he_meas : ∀ a : m, AEStronglyMeasurable (fun ω => e 0 ω a) μ :=
    fun a =>
      errorCoordinate_aestronglyMeasurable_of_linear_model
        (μ := μ) hX_meas hY_meas (fun ω j => hmodel 0 ω j) a
  have he_memLp : ∀ a : m, MemLp (fun ω => e 0 ω a) 2 μ :=
    fun a => errorCoordinate_memLp_two_of_outer_integrable
      (μ := μ) he_meas hOuter a
  exact
    ((he_memLp a).integrable_mul
      ((hX_memLp.eval b).eval l)).add
    (((hX_memLp.eval a).eval l).integrable_mul
      (he_memLp b))

namespace SURGaussianLimitConditions

omit [Fintype n] [DecidableEq n] in
/-- Constructor for Hansen Theorem 11.4 from transformed-error matrix
conditional homoskedasticity and iid observation rows.

Compared with
`of_weighted_error_matrix_conditionalHomoskedasticity`, this wrapper derives
the fixed SUR information iid fields and the weighted-score iid fields from the
single joint-row iid surface `(Xᵢ, eᵢ)`. The finite second moment for the
weighted score, its zero mean, population information nonsingularity, and the
rate-sensitive feasible `Σ̂⁻¹` beta substitution remain explicit. -/
private theorem of_weighted_error_matrix_conditionalHomoskedasticity_observation_iid_row
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hinfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_weighted_error_matrix_conditionalHomoskedasticity
    (μ := μ) (Z := Z) hX_meas hY_meas hweighted_hom
    (systemMiddleTerm_independent_of_iIndep_row
      (μ := μ) (X := X) (e := e) Sigma⁻¹ hrow_iIndep)
    (fun i =>
      systemMiddleTerm_identDistrib_of_identDistrib_row
        (μ := μ) (X := X) (e := e) Sigma⁻¹ hrow_ident i)
    hscore_memLp
    (weightedSystemScore_iIndep_of_iIndep_row
      (μ := μ) (X := X) (e := e) Sigma⁻¹ hrow_iIndep)
    (fun i =>
      weightedSystemScore_identDistrib_of_identDistrib_row
        (μ := μ) (X := X) (e := e) Sigma⁻¹ hrow_ident i)
    hscore_mean_zero hinfo_unit hSigma_posSemidef hmodel hsub

omit [Fintype n] [DecidableEq n] in
/-- Constructor for Hansen Theorem 11.4 from Assumption 7.2, transformed-error
matrix conditional homoskedasticity, and iid observation rows.

This further removes the separate population SUR information nonsingularity
premise by reusing the Chapter 11 bridge
`surInformation_nonsing_of_systemAssumption72`. The weighted-score finite
second moment, zero mean, and feasible beta substitution remain the exact
stochastic inputs not implied by the current `SystemRegressionMomentConditions` package. -/
private theorem of_weighted_matrix_hom_regression_iid_row
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_weighted_error_matrix_conditionalHomoskedasticity_observation_iid_row
    (μ := μ) (Z := Z) hX_meas hY_meas hweighted_hom
    hrow_iIndep hrow_ident hscore_memLp hscore_mean_zero
    (surInformation_nonsing_of_systemAssumption72
      (μ := μ) h72 hweighted_hom.middle_integrable hSigma_posSemidef hSigma_unit)
    hSigma_posSemidef hmodel hsub

omit [Fintype n] [DecidableEq n] in
/-- Constructor for Hansen Theorem 11.4 from transformed-error matrix
conditional homoskedasticity and iid observation rows, deriving the weighted
score `L²` field from the transformed score-middle integrability.

The weighted-score zero mean and the scaled feasible `Σ̂⁻¹` beta substitution
remain explicit for compatibility. The companion `_score_outer_exogeneity`
constructor derives the zero-mean field from `SystemConditionalMeanZero`, while
the substitution is the separate rate-sensitive step for feasible SUR. -/
private theorem of_weighted_matrix_hom_iid_row_score_outer
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hinfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_weighted_error_matrix_conditionalHomoskedasticity_observation_iid_row
    (μ := μ) (Z := Z) hX_meas hY_meas hweighted_hom hrow_iIndep hrow_ident
    (weightedSystemScore_memLp_two_of_linear_model_robust_integrable
      (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
      Sigma⁻¹ (hX_meas 0) (hY_meas 0) hmodel hweighted_hom.robust_integrable)
    hscore_mean_zero hinfo_unit hSigma_posSemidef hmodel hsub

omit [Fintype n] [DecidableEq n] in
/-- Constructor for Hansen Theorem 11.4 from transformed-error matrix
conditional homoskedasticity, iid observation rows, and conditional
mean-zero/exogeneity.

This is the score-outer constructor with the weighted-score mean-zero premise
discharged by `SystemConditionalMeanZero.score_mean_zero_of_matrixConditionalHomoskedasticity`.
The diagonal second-product integrability in the matrix homoskedasticity package
supplies the scalar product integrability needed by the conditioning argument. -/
private theorem of_weighted_error_matrix_condHomoskedasticity_iid_row_score_outer_exog
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hscore_exog : SystemConditionalMeanZero μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω))
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω)) (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hinfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_weighted_matrix_hom_iid_row_score_outer
    (μ := μ) (Z := Z) hX_meas hY_meas hweighted_hom hrow_iIndep hrow_ident
    (hscore_exog.score_mean_zero_of_matrixConditionalHomoskedasticity hweighted_hom)
    hinfo_unit hSigma_posSemidef hmodel hsub

omit [Fintype n] [DecidableEq n] in
/-- Primitive-row Assumption 7.2 constructor for Hansen Theorem 11.4 from
transformed-error matrix conditional homoskedasticity.

`SystemPrimitiveRowRegressionMomentConditions` supplies the split Assumption 7.2 fields and
joint-row iid surface; the transformed matrix homoskedasticity package supplies
the exact score covariance identity and the weighted score outer-product
integrability used to derive `MemLp`. The companion `_score_outer_exogeneity`
constructor derives weighted-score mean zero from `SystemConditionalMeanZero`;
the scaled feasible-weight substitution remains explicit. -/
private theorem of_primitive_row_weighted_matrix_hom_score_outer
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_weighted_matrix_hom_regression_iid_row
    (μ := μ) (Z := Z)
    (fun i => h72.x_aestronglyMeasurable_at i) hY_meas
    h72.toSystemRegressionMomentConditions hweighted_hom h72.row_iIndep h72.row_identDistrib
    (weightedSystemScore_memLp_two_of_linear_model_robust_integrable
      (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
      Sigma⁻¹ h72.x_aestronglyMeasurable (hY_meas 0) hmodel
      hweighted_hom.robust_integrable)
    hscore_mean_zero hSigma_posSemidef hSigma_unit hmodel hsub

omit [Fintype n] [DecidableEq n] in
/-- Primitive-row Assumption 7.2 constructor for Hansen Theorem 11.4 from
transformed-error matrix conditional homoskedasticity and conditional
mean-zero/exogeneity.

This is the current tightest fixed-`Σ⁻¹` score route: Assumption 7.2 supplies
row iid fields and SUR information nonsingularity, the transformed matrix
homoskedasticity package supplies the covariance identity and score `L²` field,
and `SystemConditionalMeanZero` supplies weighted-score mean zero. The feasible
`Σ̂⁻¹` substitution remains the separate rate-sensitive premise. -/
private theorem of_primitive_row_assumption72_weighted_error_condHomoskedasticity_score_exog
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hscore_exog : SystemConditionalMeanZero μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω))
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hsub : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          Real.sqrt (t : ℝ) •
            (surBetaFromErrorCovStar
              (fun i : Fin t => X i.val ω) Sigma (fun i : Fin t => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_primitive_row_weighted_matrix_hom_score_outer
    (μ := μ) (Z := Z) hY_meas h72 hweighted_hom
    (hscore_exog.score_mean_zero_of_matrixConditionalHomoskedasticity hweighted_hom)
    hSigma_posSemidef hSigma_unit hmodel hsub

set_option linter.style.longLine false in
/-- Fixed-score CLT package behind the primitive-row/exogeneity route for
Hansen Theorem 11.4.

This exposes the reusable constructor used by the feasible-weight constructors:
Assumption 7.2 supplies the iid information fields, transformed matrix
homoskedasticity supplies score covariance and `L²`, and conditional exogeneity
supplies the zero mean. -/
private theorem scoreCLT_of_primitive_row_weighted_hom_exog
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hscore_exog : SystemConditionalMeanZero μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω))
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    SURScoreCLTConditions μ X Sigma⁻¹ e
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]) := by
  have hscore_memLp : MemLp
      (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) 2 μ :=
    weightedSystemScore_memLp_two_of_linear_model_robust_integrable
      (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
      Sigma⁻¹ h72.x_aestronglyMeasurable (hY_meas 0) hmodel
      hweighted_hom.robust_integrable
  have hscore_mean_zero :
      meanVec μ (fun ω => systemScore (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) = 0 :=
    hscore_exog.score_mean_zero_of_matrixConditionalHomoskedasticity hweighted_hom
  exact
    SURScoreCLTConditions.of_weighted_score_moments
      (μ := μ) (X := X) (e := e) (W := Sigma⁻¹)
      hweighted_hom.middle_integrable
      (systemMiddleTerm_independent_of_iIndep_row
        (μ := μ) (X := X) (e := e) Sigma⁻¹ h72.row_iIndep)
      (fun i =>
        systemMiddleTerm_identDistrib_of_identDistrib_row
          (μ := μ) (X := X) (e := e) Sigma⁻¹ h72.row_identDistrib i)
      hscore_memLp
      (weightedSystemScore_iIndep_of_iIndep_row
        (μ := μ) (X := X) (e := e) Sigma⁻¹ h72.row_iIndep)
      (fun i =>
        weightedSystemScore_identDistrib_of_identDistrib_row
          (μ := μ) (X := X) (e := e) Sigma⁻¹ h72.row_identDistrib i)
      hscore_mean_zero
      (weightedScore_covMat_eq_middle_of_matrix_hom
        (μ := μ) (Z := Z) X e Sigma hscore_memLp hscore_mean_zero hweighted_hom)
      (surInformation_nonsing_of_systemAssumption72
        (μ := μ) h72.toSystemRegressionMomentConditions hweighted_hom.middle_integrable
        hSigma_posSemidef hSigma_unit)
      (Matrix.PosSemidef.inv hSigma_posSemidef)

/-- Primitive-row Assumption 7.2 constructor for Hansen Theorem 11.4 that
derives the feasible `Σ̂⁻¹` beta substitution from the Chapter 11 covariance
consistency package and scalar score-weight tightness.

Compared with
`of_primitive_row_assumption72_weighted_error_condHomoskedasticity_score_exog`,
this constructor no longer asks for the full scaled beta-level `oₚ(1)` gap. -/
theorem PrimitiveRow.of_score_exog_covariance
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hscore_exog : SystemConditionalMeanZero μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω))
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hcov : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma)
    (hScoreWeight : ∀ a b : m, ∀ j : k,
      BoundedInProbability μ
        (fun t ω =>
          Real.sqrt (t : ℝ) *
            surWeightedScoreScalarWeight
              (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω) a b j)) :
    SURGaussianLimitConditions μ X e Y Sigma β := by
  have hscore :=
    scoreCLT_of_primitive_row_weighted_hom_exog
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (Sigma := Sigma) (β := β) hY_meas h72 hweighted_hom hscore_exog
      hSigma_posSemidef hSigma_unit hmodel
  have hsub :=
    surBetaEstimatorStarObs_feasible_weight_substitution
      (μ := μ) (X := X) (e := e) (Y := Y) (Sigma := Sigma)
      (M := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]) (β := β)
      hscore hcov (fun i => h72.e_aestronglyMeasurable_at i) hmodel hScoreWeight
  exact
    of_primitive_row_assumption72_weighted_error_condHomoskedasticity_score_exog
      (μ := μ) (Z := Z) hY_meas h72 hweighted_hom hscore_exog
      hSigma_posSemidef hSigma_unit hmodel hsub

/-- Primitive-row Assumption 7.2 constructor for Hansen Theorem 11.4 that
derives scalar score-weight tightness by the iid scalar CLT.

The remaining stochastic inputs are a covariance-consistency package for the
feasible residual covariance and coordinatewise `L²` moments for the raw scalar
cross products `X_iaj e_ib`. Raw conditional exogeneity is transported to the
fixed `Σ⁻¹` score by `SystemConditionalMeanZero.weighted`. -/
theorem PrimitiveRow.of_raw_exog_scalarCLT
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hweighted_hom : MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹)
    (hraw_exog : SystemConditionalMeanZero μ Z X e)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hcov : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma)
    (hScalar_memLp : ∀ a b : m, ∀ j : k,
      MemLp (fun ω => X 0 ω a j * e 0 ω b) 2 μ) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  PrimitiveRow.of_score_exog_covariance
    (μ := μ) (Z := Z) hY_meas h72 hweighted_hom
    (hraw_exog.weighted Sigma⁻¹) hSigma_posSemidef hSigma_unit hmodel hcov
    (fun a b j =>
      surWeightedScoreScalarWeight_boundedInProbability_of_iid_row_condMeanZero
        (μ := μ) (Z := Z) (X := X) (e := e)
        h72.row_iIndep h72.row_identDistrib hraw_exog a b j (hScalar_memLp a b j))

end SURGaussianLimitConditions

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- A finite second moment for the matrix-valued system design row implies a
finite second moment for each coordinate. -/
private theorem designCoordinate_memLp_two_of_design_memLp_two
    {X0 : Ω → Matrix m k ℝ} (hX : MemLp X0 2 μ) (a : m) (c : k) :
    MemLp (fun ω => X0 ω a c) 2 μ :=
  (hX.eval a).eval c

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- The literal matrix `(11.8)` package supplies design coordinate
measurability, so Hansen Assumption 7.2's Gram integrability yields the
matrix-valued `L²` design moment needed by Theorem 11.5. -/
private theorem design_memLp_two_of_systemAssumption72_matrix_condHomoskedastic
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma) :
    MemLp (X 0) 2 μ :=
  systemDesign_memLp_two_of_gram_integrable_coordinates
    (μ := μ)
    (fun a c =>
      (hhom.x_conditioning_aestronglyMeasurable a c).mono
        (conditioningSpace_le hhom.conditioning_measurable))
    h72.gram_integrable

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Coordinate design products used by feasible SUR are integrable when the
system design row has a finite second moment. -/
theorem systemHomoskedasticMiddleWeight_integrable_of_design_memLp_two
    {X : ℕ → Ω → Matrix m k ℝ}
    (hX : MemLp (X 0) 2 μ) (a b : m) (c d : k) :
    Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ :=
  (designCoordinate_memLp_two_of_design_memLp_two (μ := μ) hX a c).integrable_mul
    (designCoordinate_memLp_two_of_design_memLp_two (μ := μ) hX b d)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- The fixed SUR information contribution `X'WX` is integrable when the
system design row has a finite second moment. -/
theorem systemMiddleTerm_integrable_of_design_memLp_two
    {X : ℕ → Ω → Matrix m k ℝ} (W : Matrix m m ℝ)
    (hX : MemLp (X 0) 2 μ) :
    Integrable (fun ω => systemMiddleTerm (X 0 ω) W) μ := by
  refine Integrable.of_eval ?_
  intro c
  refine Integrable.of_eval ?_
  intro d
  have hterm : Integrable
      (fun ω => ∑ a : m, ∑ b : m, W b a * (X 0 ω a d * X 0 ω b c)) μ := by
    refine integrable_finset_sum _ (fun a _ => ?_)
    refine integrable_finset_sum _ (fun b _ => ?_)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((systemHomoskedasticMiddleWeight_integrable_of_design_memLp_two
        (μ := μ) (X := X) hX a b d c).const_mul (W b a))
  simpa [systemMiddleTerm, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hterm

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
private theorem systemRobustMiddleTerm_integrable_of_weighted_error_integrable
    {X0 : Ω → Matrix m k ℝ} {u0 : Ω → m → ℝ}
    (hweighted : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X0 ω a c * X0 ω b d * (u0 ω a * u0 ω b)) μ) :
    Integrable (fun ω => systemRobustMiddleTerm (X0 ω) (u0 ω)) μ := by
  refine Integrable.of_eval ?_
  intro c
  refine Integrable.of_eval ?_
  intro d
  have hrepr :
      (fun ω => systemRobustMiddleTerm (X0 ω) (u0 ω) c d) =
        fun ω => ∑ a : m, ∑ b : m,
          X0 ω a d * (X0 ω b c * (u0 ω a * u0 ω b)) := by
    funext ω
    simp [systemRobustMiddleTerm, systemMiddleTerm, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Matrix.transpose_apply, Finset.mul_sum, mul_comm]
  rw [hrepr]
  exact integrable_finset_sum _ fun a _ =>
    integrable_finset_sum _ fun b _ =>
      by simpa [mul_assoc] using hweighted a b d c

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] in
private theorem norm_sq_memLp_two_of_norm_fourth_integrable
    {E : Type*} [NormedAddCommGroup E] {f : Ω → E}
    (hf : AEStronglyMeasurable f μ)
    (hfourth : Integrable (fun ω => ‖f ω‖ ^ 4) μ) :
    MemLp (fun ω => ‖f ω‖ ^ 2) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω => ‖f ω‖ ^ 2) μ :=
    ((hf.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  convert hfourth using 1
  ext ω
  ring

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [DecidableEq k]
  [DecidableEq m] in
/-- Compact row-fourth moments imply the raw mixed fourth-product surface used
by the feasible SUR weight substitution in Hansen Theorem 11.4. -/
theorem surMixedFourthProduct_integrable_of_rowNorm_fourth
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (he0 : AEStronglyMeasurable (e 0) μ)
    (hX_fourth : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (he_fourth : Integrable (fun ω => ‖e 0 ω‖ ^ 4) μ)
    (a b p q : m) (c d : k) :
    Integrable
      (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)) μ := by
  have hX_sq : MemLp (fun ω => ‖X 0 ω‖ ^ 2) 2 μ :=
    norm_sq_memLp_two_of_norm_fourth_integrable (μ := μ) hX0 hX_fourth
  have he_sq : MemLp (fun ω => ‖e 0 ω‖ ^ 2) 2 μ :=
    norm_sq_memLp_two_of_norm_fourth_integrable (μ := μ) he0 he_fourth
  have hnormProduct : Integrable (fun ω => ‖X 0 ω‖ ^ 2 * ‖e 0 ω‖ ^ 2) μ := by
    simpa [Pi.mul_apply] using hX_sq.integrable_mul he_sq
  have hXa : AEStronglyMeasurable (fun ω => X 0 ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable hX0
  have hXb : AEStronglyMeasurable (fun ω => X 0 ω b) μ :=
    (continuous_apply b).comp_aestronglyMeasurable hX0
  have hXac : AEStronglyMeasurable (fun ω => X 0 ω a c) μ :=
    (continuous_apply c).comp_aestronglyMeasurable hXa
  have hXbd : AEStronglyMeasurable (fun ω => X 0 ω b d) μ :=
    (continuous_apply d).comp_aestronglyMeasurable hXb
  have hep : AEStronglyMeasurable (fun ω => e 0 ω p) μ :=
    (continuous_apply p).comp_aestronglyMeasurable he0
  have heq : AEStronglyMeasurable (fun ω => e 0 ω q) μ :=
    (continuous_apply q).comp_aestronglyMeasurable he0
  have htarget : AEStronglyMeasurable
      (fun ω => X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)) μ :=
    (hXac.mul hXbd).mul (hep.mul heq)
  refine hnormProduct.mono' htarget (ae_of_all μ fun ω => ?_)
  have hXac_le : |X 0 ω a c| ≤ ‖X 0 ω‖ := by
    simpa [Real.norm_eq_abs] using
      (Matrix.norm_entry_le_entrywise_sup_norm (A := X 0 ω) (i := a) (j := c))
  have hXbd_le : |X 0 ω b d| ≤ ‖X 0 ω‖ := by
    simpa [Real.norm_eq_abs] using
      (Matrix.norm_entry_le_entrywise_sup_norm (A := X 0 ω) (i := b) (j := d))
  have hep_le : |e 0 ω p| ≤ ‖e 0 ω‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (e 0 ω) p
  have heq_le : |e 0 ω q| ≤ ‖e 0 ω‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (e 0 ω) q
  calc
    ‖X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)‖ =
        |X 0 ω a c| * |X 0 ω b d| * (|e 0 ω p| * |e 0 ω q|) := by
          simp [Real.norm_eq_abs, mul_assoc]
    _ ≤ ‖X 0 ω‖ * ‖X 0 ω‖ * (‖e 0 ω‖ * ‖e 0 ω‖) := by
          gcongr
    _ = ‖X 0 ω‖ ^ 2 * ‖e 0 ω‖ ^ 2 := by ring

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype k]
  [DecidableEq k] [DecidableEq m] in
private theorem transformed_weighted_error_integrable_of_mixed_fourth
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (W : Matrix m m ℝ)
    (hmixed : ∀ a b p q : m, ∀ c d : k,
      Integrable (fun ω =>
        X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)) μ)
    (a b : m) (c d : k) :
    Integrable
      (fun ω =>
        X 0 ω a c * X 0 ω b d *
          ((W *ᵥ e 0 ω) a * (W *ᵥ e 0 ω) b)) μ := by
  have hrepr :
      (fun ω =>
        X 0 ω a c * X 0 ω b d *
          ((W *ᵥ e 0 ω) a * (W *ᵥ e 0 ω) b)) =
        fun ω => ∑ q : m, ∑ p : m,
          (W a p * W b q) *
            (X 0 ω a c * X 0 ω b d * (e 0 ω q * e 0 ω p)) := by
    funext ω
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hrepr]
  exact integrable_finset_sum _ fun q _ =>
    integrable_finset_sum _ fun p _ =>
      (hmixed a b q p c d).const_mul (W a p * W b q)

omit [IsProbabilityMeasure μ] [Fintype n] [DecidableEq n] [Fintype k]
  [DecidableEq k] [Fintype m] [DecidableEq m] in
/-- A raw mixed fourth-moment surface gives the `L²` scalar cross-score inputs
used in Hansen Theorem 11.4's feasible SUR weight substitution. -/
private theorem surWeightedScoreScalar_memLp_two_of_mixed_fourth_integrable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hX_meas : ∀ a : m, ∀ c : k,
      AEStronglyMeasurable (fun ω => X 0 ω a c) μ)
    (he_meas : ∀ b : m, AEStronglyMeasurable (fun ω => e 0 ω b) μ)
    (hmixed : ∀ a b p q : m, ∀ c d : k,
      Integrable (fun ω =>
        X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)) μ)
    (a b : m) (j : k) :
    MemLp (fun ω => X 0 ω a j * e 0 ω b) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω => X 0 ω a j * e 0 ω b) μ :=
    (hX_meas a j).mul (he_meas b)
  have hsq : Integrable (fun ω => (X 0 ω a j * e 0 ω b) ^ 2) μ := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      hmixed a a b b j j
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq

namespace MatrixSystemConditionalHomoskedasticity

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Raw Hansen `(11.8)` plus mixed fourth-product integrability implies the
transformed-error `(Σ⁻¹e)` homoskedasticity package used by Hansen Theorem 11.4.

The mixed fourth-product surface is the non-tautological side condition needed
because `(Σ⁻¹e)_a(Σ⁻¹e)_b` expands into arbitrary products
`X_{ic}X_{id}e_{ip}e_{iq}` rather than only the tied products in
`X_i'e_ie_i'X_i`. -/
theorem inverseWeighted_of_mixed_fourth_integrable
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef)
    (hX_memLp : MemLp (X 0) 2 μ)
    (hmixed : ∀ a b p q : m, ∀ c d : k,
      Integrable (fun ω =>
        X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)) μ) :
    MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹ := by
  have hweighted_error : ∀ a b : m, ∀ c d : k,
      Integrable
        (fun ω =>
          X 0 ω a c * X 0 ω b d *
            ((Sigma⁻¹ *ᵥ e 0 ω) a * (Sigma⁻¹ *ᵥ e 0 ω) b)) μ :=
    fun a b c d =>
      transformed_weighted_error_integrable_of_mixed_fourth
        (μ := μ) (X := X) (e := e) Sigma⁻¹ hmixed a b c d
  have hrobust : Integrable
      (fun ω => systemRobustMiddleTerm (X 0 ω) (Sigma⁻¹ *ᵥ e 0 ω)) μ :=
    systemRobustMiddleTerm_integrable_of_weighted_error_integrable
      (μ := μ) hweighted_error
  have hmiddle : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ :=
    systemMiddleTerm_integrable_of_design_memLp_two (μ := μ) (X := X) Sigma⁻¹ hX_memLp
  have hweighted_sigma : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d * Sigma⁻¹ a b) μ := by
    intro a b c d
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (systemHomoskedasticMiddleWeight_integrable_of_design_memLp_two
        (μ := μ) (X := X) hX_memLp a b c d).const_mul (Sigma⁻¹ a b)
  exact h.inverseWeighted hSigma hrobust hmiddle hweighted_error hweighted_sigma

omit [Fintype n] [DecidableEq n] in
/-- Assumption 7.2 supplies the design `L²` moment in the raw-to-transformed
Hansen `(11.8)` bridge. -/
theorem inverseWeighted_of_systemAssumption72_mixed_fourth_integrable
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hSigma : Sigma.PosDef)
    (hmixed : ∀ a b p q : m, ∀ c d : k,
      Integrable (fun ω =>
        X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)) μ) :
    MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹ :=
  h.inverseWeighted_of_mixed_fourth_integrable
    (μ := μ) hSigma
    (design_memLp_two_of_systemAssumption72_matrix_condHomoskedastic
      (μ := μ) h72 h)
    hmixed

omit [Fintype n] [DecidableEq n] in
/-- Compact row-fourth moments discharge the mixed-product side condition in
the raw-to-transformed `(11.8)` bridge. -/
private theorem inverseWeighted_of_systemAssumption72_rowNorm_fourth
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (h : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hSigma : Sigma.PosDef)
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (he0 : AEStronglyMeasurable (e 0) μ)
    (hX_fourth : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (he_fourth : Integrable (fun ω => ‖e 0 ω‖ ^ 4) μ) :
    MatrixSystemConditionalHomoskedasticity μ Z X
      (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹ :=
  h.inverseWeighted_of_systemAssumption72_mixed_fourth_integrable
    (μ := μ) h72 hSigma
    (fun a b p q c d =>
      surMixedFourthProduct_integrable_of_rowNorm_fourth
        (μ := μ) (X := X) (e := e) hX0 he0 hX_fourth he_fourth a b p q c d)

end MatrixSystemConditionalHomoskedasticity

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 from `SystemRegressionMomentConditions` and the literal
matrix-valued `(11.8)` package, with SUR information integrability derived
from square-integrability of the design row. -/
private theorem sur_efficiency_of_systemAssumption72_matrix_condHomoskedastic_memLp
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX : MemLp (X 0) 2 μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_of_matrix_regression_hom
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72 hhom
    (systemMiddleTerm_integrable_of_design_memLp_two (μ := μ) (X := X) Sigma⁻¹ hX)
    hSigma hSigma_unit hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation endpoint from `SystemRegressionMomentConditions`
and literal matrix homoskedasticity, deriving fixed SUR information
integrability from square-integrability of the design row. -/
private theorem sur_efficiency_scoreCov_of_systemAssumption72_matrix_condHomoskedastic_memLp
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX : MemLp (X 0) 2 μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance M).PosSemidef :=
  sur_scoreCov_efficiency_of_matrix_regression_hom
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72 hhom
    (systemMiddleTerm_integrable_of_design_memLp_two (μ := μ) (X := X) Sigma⁻¹ hX)
    hSigma hSigma_unit hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 literal-information endpoint, deriving
`E[Xᵢ'Σ⁻¹Xᵢ]` integrability from square-integrability of the design row. -/
private theorem sur_efficiency_of_assumption72_matrix_condHomoskedastic_surInfo_memLp
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX : MemLp (X 0) 2 μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef := by
  let hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ :=
    systemMiddleTerm_integrable_of_design_memLp_two (μ := μ) (X := X) Sigma⁻¹ hX
  exact
    sur_efficiency_of_matrix_hom
      (μ := μ) (X := X) (e := e) (Sigma := Sigma)
      h72 hhom hSUR hSigma hSigma_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation literal-information endpoint,
deriving `E[Xᵢ'Σ⁻¹Xᵢ]` integrability from square-integrability of the design
row. -/
private theorem sur_efficiency_scoreCov_of_assumption72_matrix_condHomoskedastic_surInfo_memLp
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX : MemLp (X 0) 2 μ)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef := by
  let hSUR : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ :=
    systemMiddleTerm_integrable_of_design_memLp_two (μ := μ) (X := X) Sigma⁻¹ hX
  exact
    sur_scoreCov_efficiency_of_matrix_hom
      (μ := μ) (X := X) (e := e) (Sigma := Sigma)
      h72 hhom hSUR hSigma hSigma_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 from `SystemRegressionMomentConditions` and the literal
matrix-valued `(11.8)` package, deriving the SUR information integrability
directly from Assumption 7.2's Gram integrability. -/
private theorem sur_efficiency_of_systemAssumption72_matrix_condHomoskedastic_of_gram
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_of_systemAssumption72_matrix_condHomoskedastic_memLp
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72 hhom
    (design_memLp_two_of_systemAssumption72_matrix_condHomoskedastic
      (μ := μ) h72 hhom)
    hSigma hSigma_unit hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation endpoint from `SystemRegressionMomentConditions`
and literal matrix homoskedasticity, deriving the fixed SUR information
integrability directly from Assumption 7.2's Gram integrability. -/
private theorem sur_efficiency_scoreCov_of_systemAssumption72_matrix_condHomoskedastic_of_gram
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (M : Matrix k k ℝ) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det)
    (hM : systemPopulationMiddle μ (fun ω => X 0 ω) Sigma⁻¹ = M)
    (hM_unit : IsUnit M.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance M).PosSemidef :=
  sur_efficiency_scoreCov_of_systemAssumption72_matrix_condHomoskedastic_memLp
    (μ := μ) (M := M) (X := X) (e := e) (Sigma := Sigma)
    h72 hhom
    (design_memLp_two_of_systemAssumption72_matrix_condHomoskedastic
      (μ := μ) h72 hhom)
    hSigma hSigma_unit hM hM_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 literal-information endpoint, deriving
`E[Xᵢ'Σ⁻¹Xᵢ]` integrability directly from Assumption 7.2's Gram
integrability. -/
private theorem sur_efficiency_of_assumption72_matrix_condHomoskedastic_surInfo_of_gram
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationScoreCovariance μ X e) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef :=
  sur_efficiency_of_assumption72_matrix_condHomoskedastic_surInfo_memLp
    (μ := μ) (X := X) (e := e) (Sigma := Sigma)
    h72 hhom
    (design_memLp_two_of_systemAssumption72_matrix_condHomoskedastic
      (μ := μ) h72 hhom)
    hSigma hSigma_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 covariance-notation literal-information endpoint,
deriving `E[Xᵢ'Σ⁻¹Xᵢ]` integrability directly from Assumption 7.2's Gram
integrability. -/
private theorem sur_efficiency_scoreCov_of_assumption72_matrix_condHomoskedastic_surInfo_of_gram
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω))) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef :=
  sur_efficiency_scoreCov_of_assumption72_matrix_condHomoskedastic_surInfo_memLp
    (μ := μ) (X := X) (e := e) (Sigma := Sigma)
    h72 hhom
    (design_memLp_two_of_systemAssumption72_matrix_condHomoskedastic
      (μ := μ) h72 hhom)
    hSigma hSigma_unit

omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 displayed-population-middle endpoint.

This is the literal matrix `(11.8)` Assumption-7.2 wrapper with the least-squares
variance written in Hansen's displayed `E[Xᵢ'ΣXᵢ]` notation and the SUR side
written as `(E[Xᵢ'Σ⁻¹Xᵢ])⁻¹`. The proof reuses the score-covariance identity
from `MatrixSystemConditionalHomoskedasticity`. -/
private theorem sur_efficiency_display_of_assumption72_matrix_condHomoskedastic_surInfo_of_gram
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationMiddle μ (fun ω => X 0 ω) Sigma) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef := by
  rw [← hhom.scoreCovariance_eq_middle]
  exact
    sur_efficiency_of_assumption72_matrix_condHomoskedastic_surInfo_of_gram
      (μ := μ) (X := X) (e := e) (Sigma := Sigma)
      h72 hhom hSigma hSigma_unit

set_option linter.style.longLine false in
omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.5 displayed-population-middle endpoint from the literal
primitive-row Assumption 7.2 surface. -/
private theorem sur_efficiency_display_of_primitive_rows
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosSemidef) (hSigma_unit : IsUnit Sigma.det) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationMiddle μ (fun ω => X 0 ω) Sigma) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef :=
  sur_efficiency_display_of_assumption72_matrix_condHomoskedastic_surInfo_of_gram
    (μ := μ) (X := X) (e := e) (Sigma := Sigma)
    h72.toSystemRegressionMomentConditions hhom hSigma hSigma_unit

omit [Fintype n] [DecidableEq n] in
/-- **Hansen Theorem 11.5** from the literal observed-row Assumption 7.2
surface and matrix conditional homoskedasticity `(11.8)`.

The proof is a thin wrapper around the population Gauss-Markov comparison;
the observed-row package supplies the primitive Assumption 7.2 facts and
positive-definite `Sigma` supplies the inverse used by Hansen's display. -/
theorem SURTheorem11_5.efficiency_of_observed_rows
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h72 : SystemObservedResponseFourthMomentConditions μ X e Y β)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef) :
    (systemAsymptoticVariance (systemPopulationGram μ X)
        (systemPopulationMiddle μ (fun ω => X 0 ω) Sigma) -
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])).PosSemidef :=
  sur_efficiency_display_of_primitive_rows
    (μ := μ) (X := X) (e := e) (Sigma := Sigma)
    h72.toSystemPrimitiveRowRegressionMomentConditions hhom hSigma.posSemidef
    ((Matrix.isUnit_iff_isUnit_det Sigma).mp hSigma.isUnit)

namespace SURCovarianceEstimatorConsistencyConditions

omit [Fintype n] [DecidableEq n] in
/-- Feasible-SUR covariance-consistency constructor from observation-level iid design.

This closes the independence and identical-distribution fields for both the
fixed SUR information WLLN and the scalar design-weight WLLNs from the single
primitive `iIndepFun X` / `IdentDistrib Xᵢ X₀` design surface. The residual
covariance consistency `Σ̂ ->p Σ`, fixed information integrability, scalar
second-moment integrability, and nonsingularity assumptions remain explicit. -/
theorem of_observation_iid_design
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hX_iIndep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hSigmaHat : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => Sigma))
    (hSigma_unit : IsUnit Sigma.det)
    (hInfo_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hInfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma where
  x_aestronglyMeasurable := hX_meas
  y_aestronglyMeasurable := hY_meas
  residual_covariance_tendsto := hSigmaHat
  error_covariance_nonsing := hSigma_unit
  information_integrable := hInfo_int
  information_independent :=
    systemMiddleTerm_independent_of_iIndep_design
      (μ := μ) (X := X) Sigma⁻¹ hX_iIndep
  information_identDistrib :=
    systemMiddleTerm_identDistrib_of_identDistrib_design
      (μ := μ) (X := X) Sigma⁻¹ hX_ident
  design_weight_integrable := hWeight_int
  design_weight_independent :=
    fun a b c d =>
      systemHomoskedasticMiddleWeight_independent_of_iIndep_design
        (μ := μ) (X := X) hX_iIndep a b c d
  design_weight_identDistrib :=
    fun a b c d =>
      systemHomoskedasticMiddleWeight_identDistrib_of_identDistrib_design
        (μ := μ) (X := X) hX_ident a b c d
  information_nonsing := hInfo_unit

omit [Fintype n] [DecidableEq n] in
/-- Feasible-SUR covariance-consistency constructor from literal matrix conditional
homoskedasticity, true-error covariance WLLN, and observation-level iid design.

The literal matrix `(11.8)` package pins the true error covariance target to
`Σ`. The true-error outer-product WLLN plus the residual-covariance
substitution gives `Σ̂ ->p Σ`; observation-level iid design supplies the fixed
SUR information and design-weight independence/identical-distribution fields.
The remaining assumptions are exactly the fixed information/design integrability
and nonsingularity facts not implied by the current Assumption 7.2 package. -/
theorem of_matrix_conditionalHomoskedasticity_observation_iid_design
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX_iIndep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hErrorOuter_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))))
    (hErrorOuter_ident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ)
    (hResidualCov_sub : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) -
          systemSigmaHat (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0))
    (hSigma_unit : IsUnit Sigma.det)
    (hInfo_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hInfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
  of_observation_iid_design
    (μ := μ) (X := X) (Y := Y) hX_meas hY_meas hX_iIndep hX_ident
    (surResidualCovarianceStarObs_tendstoInMeasure_of_true_error_substitution
      (μ := μ) (X := X) (e := e) (Y := Y)
      (hhom.trueErrorResidualCovariance_tendstoInMeasure
        hErrorOuter_indep hErrorOuter_ident)
      hResidualCov_sub)
    hSigma_unit hInfo_int hWeight_int hInfo_unit

omit [Fintype n] [DecidableEq n] in
/-- Feasible-SUR covariance-consistency constructor from literal matrix conditional
homoskedasticity, observation-level iid design, and a finite second moment for
the design row.

Compared with the observation-iid matrix-homoskedasticity constructor, this
wrapper derives the fixed SUR information integrability and scalar design-weight
integrability fields from the single finite-second-moment design premise. The
residual-covariance substitution and population information nonsingularity
remain the substantive Hansen-facing inputs. -/
private theorem of_matrix_conditionalHomoskedasticity_observation_iid_design_memLp
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX_iIndep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hErrorOuter_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))))
    (hErrorOuter_ident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ)
    (hResidualCov_sub : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) -
          systemSigmaHat (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0))
    (hSigma_unit : IsUnit Sigma.det)
    (hX_memLp : MemLp (X 0) 2 μ)
    (hInfo_unit : IsUnit
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]).det) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
  of_matrix_conditionalHomoskedasticity_observation_iid_design
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (Sigma := Sigma)
    hX_meas hY_meas hhom hX_iIndep hX_ident
    hErrorOuter_indep hErrorOuter_ident hResidualCov_sub hSigma_unit
    (systemMiddleTerm_integrable_of_design_memLp_two
      (μ := μ) (X := X) Sigma⁻¹ hX_memLp)
    (fun a b c d =>
      systemHomoskedasticMiddleWeight_integrable_of_design_memLp_two
        (μ := μ) (X := X) hX_memLp a b c d)
    hInfo_unit

omit [Fintype n] [DecidableEq n] in
/-- Feasible-SUR covariance-consistency constructor from Assumption 7.2, literal matrix
conditional homoskedasticity, true-error covariance WLLN, and
observation-level iid design.

Compared with `of_matrix_conditionalHomoskedasticity_observation_iid_design`,
this wrapper derives the population SUR information nonsingularity
`det E[Xᵢ'Σ⁻¹Xᵢ] ≠ 0` from Assumption 7.2 plus positive-definiteness of `Σ`.
The fixed information/design integrability fields are still supplied
explicitly in this version. -/
theorem of_matrix_conditionalHomoskedasticity_systemAssumption72_observation_iid_design
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX_iIndep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hErrorOuter_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))))
    (hErrorOuter_ident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ)
    (hResidualCov_sub : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) -
          systemSigmaHat (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0))
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hInfo_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹) μ)
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
  of_matrix_conditionalHomoskedasticity_observation_iid_design
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (Sigma := Sigma)
    hX_meas hY_meas hhom hX_iIndep hX_ident
    hErrorOuter_indep hErrorOuter_ident hResidualCov_sub hSigma_unit
    hInfo_int hWeight_int
    (surInformation_nonsing_of_systemAssumption72
      (μ := μ) h72 hInfo_int hSigma_posSemidef hSigma_unit)

omit [Fintype n] [DecidableEq n] in
/-- Feasible-SUR covariance-consistency constructor from Assumption 7.2, literal matrix
conditional homoskedasticity, observation-level iid design, and a finite second
moment for the design row.

This is the smallest current constructor for the fixed-information side of
the corrected feasible-SUR covariance result: it derives information integrability, scalar
design-weight integrability, and population SUR information nonsingularity
from `MemLp (X 0) 2 μ`, Assumption 7.2, and positive-definiteness of `Σ`. -/
private theorem of_matrix_hom_regression_iid_design
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX_iIndep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hErrorOuter_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))))
    (hErrorOuter_ident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ)
    (hResidualCov_sub : TendstoInMeasure μ
      (fun t ω =>
        systemSigmaHatStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) -
          systemSigmaHat (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0))
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hX_memLp : MemLp (X 0) 2 μ) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
  of_matrix_conditionalHomoskedasticity_systemAssumption72_observation_iid_design
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (Sigma := Sigma)
    hX_meas hY_meas h72 hhom hX_iIndep hX_ident
    hErrorOuter_indep hErrorOuter_ident hResidualCov_sub
    hSigma_posSemidef hSigma_unit
    (systemMiddleTerm_integrable_of_design_memLp_two
      (μ := μ) (X := X) Sigma⁻¹ hX_memLp)
    (fun a b c d =>
      systemHomoskedasticMiddleWeight_integrable_of_design_memLp_two
        (μ := μ) (X := X) hX_memLp a b c d)

omit [Fintype n] [DecidableEq n] in
/-- Feasible-SUR covariance-consistency constructor from Assumption 7.2, literal matrix
conditional homoskedasticity, observation-level iid design, finite design
second moment, and residual-covariance cross WLLNs.

This is the theorem-facing residual-substitution facade for
`Σ̂(ê)-Σ̂(e)=oₚ(1)`. It reuses Theorem 11.1 coefficient consistency from
`SystemRegressionMomentConditions`, discharges the finite-sample residual algebra internally,
and derives the quadratic design-weight WLLNs from the existing iid-design and
`MemLp (X 0) 2 μ` inputs. The only residual-substitution stochastic fields left
explicit are the cross error/design WLLNs
`n⁻¹∑(e_{ia}X_{ib,l}+X_{ia,l}e_{ib})=Oₚ(1)`. -/
private theorem of_matrix_hom_regression_residual_wlln
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hX_iIndep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hErrorOuter_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))))
    (hErrorOuter_ident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hX_memLp : MemLp (X 0) 2 μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hbeta_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hCross_indep : ∀ a b : m, ∀ l : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => e i ω a * X i ω b l + X i ω a l * e i ω b)))
    (hCross_ident : ∀ a b : m, ∀ l : k, ∀ i,
      IdentDistrib
        (fun ω => e i ω a * X i ω b l + X i ω a l * e i ω b)
        (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ μ) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
  of_matrix_hom_regression_iid_design
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (Sigma := Sigma)
    hX_meas hY_meas h72 hhom hX_iIndep hX_ident
    hErrorOuter_indep hErrorOuter_ident
    (by
      simpa [systemSigmaHat] using
        (SystemFeasible.sigmaHat_sub_zero_of_beta_weight_wlln
          (μ := μ) (X := X) (e := e) (Y := Y) (β := β) hmodel
          (systemLeastSquaresBetaStarObs_tendstoInMeasure_beta
            (μ := μ) (X := X) (e := e) (Y := Y)
            h72.toSystemScoreCLTConditions β hmodel hbeta_meas)
          hCross_int hCross_indep hCross_ident
          (fun a b l r =>
            systemHomoskedasticMiddleWeight_integrable_of_design_memLp_two
              (μ := μ) (X := X) hX_memLp a b l r)
          (fun a b l r =>
            systemHomoskedasticMiddleWeight_independent_of_iIndep_design
              (μ := μ) (X := X) hX_iIndep a b l r)
          (fun a b l r i =>
            systemHomoskedasticMiddleWeight_identDistrib_of_identDistrib_design
              (μ := μ) (X := X) hX_ident a b l r i)))
    hSigma_posSemidef hSigma_unit hX_memLp

/-- Feasible-SUR covariance-consistency constructor from Assumption 7.2, literal matrix
conditional homoskedasticity `(11.8)`, joint observation iid, and a finite
second moment for the design row.

Compared with
`of_matrix_hom_regression_residual_wlln`,
this wrapper derives the design iid fields, true-error outer-product iid fields,
and residual cross-weight iid fields from the single joint-row iid surface
`(Xᵢ,eᵢ)`. The residual cross-weight integrability is derived from the linear
model, `MemLp (X 0) 2 μ`, and the error outer-product integrability already
contained in the literal matrix `(11.8)` package. -/
theorem of_assumption72_iid_row_residual_wlln_memLp
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω))
        (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hX_memLp : MemLp (X 0) 2 μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hbeta_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
  of_matrix_hom_regression_residual_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (Sigma := Sigma) (β := β)
    hX_meas hY_meas h72 hhom
    (design_iIndep_of_iIndep_row (μ := μ) hrow_iIndep)
    (fun i => design_identDistrib_of_identDistrib_row (μ := μ) hrow_ident i)
    (errorOuter_independent_of_iIndep_row (μ := μ) hrow_iIndep)
    (fun i => errorOuter_identDistrib_of_identDistrib_row (μ := μ) hrow_ident i)
    hSigma_posSemidef hSigma_unit hX_memLp hmodel hbeta_meas
    (fun a b l =>
      residualCrossWeight_integrable_of_model_memLp
        (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
        (hX_meas 0) (hY_meas 0) hmodel hX_memLp hhom.error_outer_integrable a b l)
    (fun a b l =>
      residualCrossWeight_independent_of_iIndep_row
        (μ := μ) (X := X) (e := e) hrow_iIndep a b l)
    (fun a b l i =>
      residualCrossWeight_identDistrib_of_identDistrib_row
        (μ := μ) (X := X) (e := e) hrow_ident a b l i)

/-- Feasible-SUR covariance-consistency constructor from Assumption 7.2, literal matrix
conditional homoskedasticity `(11.8)`, and joint observation iid.

This variant removes the explicit design `L²` premise from
`of_assumption72_iid_row_residual_wlln_memLp`: the design moment is derived
from `SystemRegressionMomentConditions.gram_integrable` using the coordinate measurability in
the matrix `(11.8)` package. -/
theorem of_assumption72_iid_row_residual_wlln_of_gram
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hrow_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hrow_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω))
        (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hbeta_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
  of_assumption72_iid_row_residual_wlln_memLp
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (Sigma := Sigma) (β := β)
    hX_meas hY_meas h72 hhom hrow_iIndep hrow_ident
    hSigma_posSemidef hSigma_unit
    (design_memLp_two_of_systemAssumption72_matrix_condHomoskedastic
      (μ := μ) h72 hhom)
    hmodel hbeta_meas

/-- Primitive-row Assumption 7.2 constructor for feasible-SUR covariance consistency.

This is the current tightest condition-package route for the corrected covariance result:
`SystemPrimitiveRowRegressionMomentConditions` supplies the split Assumption 7.2 fields and
the joint-row iid surface; literal matrix `(11.8)` supplies the true error
covariance target and error second moments; and the remaining residual
substitution, true-error covariance, fixed-information WLLN, and design-weight
WLLN inputs are derived internally. -/
private theorem of_primitive_row_assumption72_residual_wlln_of_gram
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
  of_assumption72_iid_row_residual_wlln_of_gram
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (Sigma := Sigma) (β := β)
    hX_meas hY_meas h72.toSystemRegressionMomentConditions hhom
    h72.row_iIndep h72.row_identDistrib hSigma_posSemidef hSigma_unit hmodel
    (fun t =>
      systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
        (μ := μ) (X := X) (e := e) (Y := Y)
        h72.toSystemRegressionMomentConditions β hmodel t)

end SURCovarianceEstimatorConsistencyConditions

/-- Corrected feasible-SUR covariance consistency, primitive-row route.

Under the Chapter 11 primitive-row Assumption 7.2 surface and the literal
matrix conditional homoskedasticity condition `(11.8)`, Hansen's feasible SUR
covariance estimator
`(n⁻¹∑ Xᵢ'Σ̂⁻¹Xᵢ)⁻¹` is consistent for
`(E[Xᵢ'Σ⁻¹Xᵢ])⁻¹`. -/
theorem surCovarianceEstimatorStarObs_consistent_of_primitive_row_assumption72
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma_posSemidef : Sigma.PosSemidef)
    (hSigma_unit : IsUnit Sigma.det)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  (SURCovarianceEstimatorConsistencyConditions.of_primitive_row_assumption72_residual_wlln_of_gram
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (Sigma := Sigma) (β := β)
      hX_meas hY_meas h72 hhom hSigma_posSemidef hSigma_unit
      hmodel).covarianceEstimator_consistent

omit [Fintype n] [DecidableEq n] in
/-- Corrected feasible-SUR covariance consistency, primitive-row positive-definite route.

This is the public wrapper for the usual positive-definite covariance
matrix condition in `(11.8)`. It derives the semidefinite and nonsingularity
inputs needed by the lower-level covariance-estimator route from
`Sigma.PosDef`, and derives the observation-level design measurability from
primitive-row Assumption 7.2. -/
theorem surCovarianceEstimatorStarObs_consistent_of_primitive_row_assumption72_posDef
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovarianceEstimatorStarObs_consistent_of_primitive_row_assumption72
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (Sigma := Sigma) (β := β)
    (fun i => h72.x_aestronglyMeasurable_at i) hY_meas h72 hhom
    hSigma.posSemidef ((Matrix.isUnit_iff_isUnit_det Sigma).mp hSigma.isUnit)
    hmodel

set_option linter.style.longLine false in
omit [Fintype n] [DecidableEq n] in
/-- Corrected feasible-SUR covariance consistency with
outcome measurability derived from the system linear model.

Hansen's display prints the probability limit as the OLS variance `Vβ`, but
the estimator immediately above the theorem is the feasible SUR covariance
and its correct limit is the SUR variance `Vβ* = (E[Xᵢ'Σ⁻¹Xᵢ])⁻¹`. Theorem
11.5 shows that `Vβ*` and `Vβ` generally differ. -/
private theorem surCovariance_consistent_of_primitive_rows
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovarianceEstimatorStarObs_consistent_of_primitive_row_assumption72_posDef
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (Sigma := Sigma) (β := β)
    (systemOutcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
      (fun i => h72.x_aestronglyMeasurable_at i)
      (fun i => h72.e_aestronglyMeasurable_at i)
      hmodel)
    h72 hhom hSigma hmodel

omit [Fintype n] [DecidableEq n] in
/-- Corrected feasible-SUR covariance consistency from the literal observed-row
Assumption 7.2 surface and matrix conditional homoskedasticity `(11.8)`.

Hansen's printed Theorem 11.6 gives the OLS target `Vβ`, but the estimator in
that theorem converges to the feasible-SUR target
`Vβ* = (E[Xᵢ'Σ⁻¹Xᵢ])⁻¹`. The two targets generally differ by Theorem 11.5. -/
theorem SURCovarianceEstimator.consistent_of_observed_rows
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h72 : SystemObservedResponseFourthMomentConditions μ X e Y β)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef) :
    CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  surCovariance_consistent_of_primitive_rows
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (Sigma := Sigma) (β := β)
    h72.toSystemPrimitiveRowRegressionMomentConditions hhom hSigma h72.model

omit [Fintype n] [DecidableEq n] in
/-- Diagnostic for the target misprint in Hansen Theorem 11.6.

If the same feasible-SUR covariance estimator converged to Hansen's printed
OLS target, uniqueness of convergence in measure would force the OLS and SUR
asymptotic variances to be equal. Theorem 11.5 permits a strict variance gap,
so the printed conclusion does not follow from Assumption 7.2 and `(11.8)` in
general. -/
theorem SURTheorem11_6.printed_target_forces_sur_ols_equality
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h72 : SystemObservedResponseFourthMomentConditions μ X e Y β)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hSigma : Sigma.PosDef)
    (hprinted : CovarianceEstimatorConsistent μ
      (fun t ω =>
        surCovarianceEstimatorStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      (systemAsymptoticVariance
        (systemPopulationGram μ X)
        (systemPopulationMiddle μ (fun ω => X 0 ω) Sigma))) :
    systemAsymptoticVariance
        (systemPopulationGram μ X)
        (systemPopulationMiddle μ (fun ω => X 0 ω) Sigma) =
      surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]) := by
  have hcorrect := SURCovarianceEstimator.consistent_of_observed_rows
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (Sigma := Sigma) (β := β) h72 hhom hSigma
  have htargets :=
    tendstoInMeasure_ae_unique hprinted.consistent hcorrect.consistent
  simpa using integral_congr_ae htargets

namespace SURGaussianLimitConditions

set_option linter.style.longLine false in
omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 constructor from raw matrix `(11.8)`, raw conditional
exogeneity, primitive-row Assumption 7.2, covariance consistency, and mixed
fourth-product integrability.

Compared with
`PrimitiveRow.of_raw_exog_scalarCLT`,
this wrapper derives both the transformed-error homoskedasticity package for
`Σ⁻¹e` and the scalar cross-score `L²` inputs from raw Hansen-facing data. -/
private theorem of_raw_hom_exog_covariance_mixed_fourth
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hraw_exog : SystemConditionalMeanZero μ Z X e)
    (hSigma : Sigma.PosDef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hcov : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma)
    (hmixed : ∀ a b p q : m, ∀ c d : k,
      Integrable (fun ω =>
        X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)) μ) :
    SURGaussianLimitConditions μ X e Y Sigma β := by
  have hSigma_unit : IsUnit Sigma.det :=
    (Matrix.isUnit_iff_isUnit_det Sigma).mp hSigma.isUnit
  have hweighted_hom :
      MatrixSystemConditionalHomoskedasticity μ Z X
        (fun i ω => Sigma⁻¹ *ᵥ e i ω) Sigma⁻¹ :=
    hhom.inverseWeighted_of_mixed_fourth_integrable
      (μ := μ) hSigma
      (SystemPrimitiveRowRegressionMomentConditions.design_memLp_two (μ := μ) h72)
      hmixed
  exact
    PrimitiveRow.of_raw_exog_scalarCLT
      (μ := μ) (Z := Z) hY_meas h72 hweighted_hom hraw_exog
      hSigma.posSemidef hSigma_unit hmodel hcov
      (fun a b j =>
        surWeightedScoreScalar_memLp_two_of_mixed_fourth_integrable
          (μ := μ) (X := X) (e := e)
          (fun a c =>
            (hhom.x_conditioning_aestronglyMeasurable a c).mono
              (conditioningSpace_le hhom.conditioning_measurable))
          (fun b => (hraw_exog.error_integrable b).aestronglyMeasurable)
          hmixed a b j)

set_option linter.style.longLine false in
omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 primitive-row endpoint using the existing SUR
residual-covariance consistency route.

This theorem derives the feasible residual covariance/rank inputs from
primitive-row Assumption 7.2 and raw matrix `(11.8)`, then applies the mixed
fourth-product constructor above. The remaining explicit primitive is the
mixed fourth-product integrability surface needed for arbitrary SUR
score-weight coordinates. -/
private theorem of_primitive_row_assumption72_raw_condHomoskedasticity_raw_exog_mixed_fourth
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hraw_exog : SystemConditionalMeanZero μ Z X e)
    (hSigma : Sigma.PosDef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmixed : ∀ a b p q : m, ∀ c d : k,
      Integrable (fun ω =>
        X 0 ω a c * X 0 ω b d * (e 0 ω p * e 0 ω q)) μ) :
    SURGaussianLimitConditions μ X e Y Sigma β := by
  have hSigma_unit : IsUnit Sigma.det :=
    (Matrix.isUnit_iff_isUnit_det Sigma).mp hSigma.isUnit
  have hcov : SURCovarianceEstimatorConsistencyConditions μ X Y Sigma :=
    SURCovarianceEstimatorConsistencyConditions.of_primitive_row_assumption72_residual_wlln_of_gram
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (Sigma := Sigma) (β := β)
      (fun i => h72.x_aestronglyMeasurable_at i) hY_meas h72 hhom
      hSigma.posSemidef hSigma_unit hmodel
  exact
    of_raw_hom_exog_covariance_mixed_fourth
      (μ := μ) (Z := Z) hY_meas h72 hhom hraw_exog hSigma hmodel hcov hmixed

set_option linter.style.longLine false in
omit [Fintype n] [DecidableEq n] in
/-- Hansen Theorem 11.4 primitive-row endpoint using raw matrix `(11.8)`, raw
conditional exogeneity, and compact row-fourth moments.

The residual-covariance consistency and rank inputs are derived internally from
primitive-row Assumption 7.2 and `(11.8)`. -/
private theorem of_primitive_row_assumption72_raw_condHomoskedasticity_raw_exog_rowNorm_fourth
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (h72 : SystemPrimitiveRowRegressionMomentConditions μ X e)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hraw_exog : SystemConditionalMeanZero μ Z X e)
    (hSigma : Sigma.PosDef)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hX_fourth : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (he_fourth : Integrable (fun ω => ‖e 0 ω‖ ^ 4) μ) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_primitive_row_assumption72_raw_condHomoskedasticity_raw_exog_mixed_fourth
    (μ := μ) (Z := Z) hY_meas h72 hhom hraw_exog hSigma hmodel
    (fun a b p q c d =>
      surMixedFourthProduct_integrable_of_rowNorm_fourth
        (μ := μ) (X := X) (e := e)
        h72.x_aestronglyMeasurable h72.e_aestronglyMeasurable
        hX_fourth he_fourth a b p q c d)

end SURGaussianLimitConditions

omit [Fintype n] [DecidableEq n] in
/-- Theorem-facing compact primitive-row facade for Hansen Theorem 11.4.

This packages the current tight SUR route for the feasible `Σ̂⁻¹` estimator:
primitive-row Assumption 7.2, literal matrix conditional homoskedasticity
`(11.8)`, raw conditional mean zero, positive-definite `Σ`, the system linear
model, and compact fourth moments for the design row and system error row.
The compact fourth moments discharge the mixed weighted-product integrability
surface used by the feasible-weight substitution. -/
structure SURPrimitiveRowGaussianLimitConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ζ : Type*} [MeasurableSpace ζ] (Z : Ω → ζ)
    (X : ℕ → Ω → Matrix m k ℝ) (e Y : ℕ → Ω → m → ℝ)
    (Sigma : Matrix m m ℝ) (β : k → ℝ) : Prop
    extends SystemPrimitiveRowRegressionMomentConditions μ X e where
  /-- Observation-level measurability for the outcome systems. -/
  y_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (Y i) μ
  /-- Hansen's literal matrix conditional homoskedasticity condition `(11.8)`. -/
  conditional_homoskedasticity :
    MatrixSystemConditionalHomoskedasticity μ Z X e Sigma
  /-- Raw conditional exogeneity used to center the feasible weight-substitution scores. -/
  conditional_mean_zero : SystemConditionalMeanZero μ Z X e
  /-- Positive definiteness of the system error covariance matrix. -/
  error_covariance_posDef : Sigma.PosDef
  /-- System linear model, observation by observation and equation by equation. -/
  linear_model : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j
  /-- Compact finite fourth moment for the system design row. -/
  design_norm_fourth_integrable : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ
  /-- Compact finite fourth moment for the system error row. -/
  error_norm_fourth_integrable : Integrable (fun ω => ‖e 0 ω‖ ^ 4) μ

namespace SURPrimitiveRowGaussianLimitConditions

open SURGaussianLimitConditions

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- Literal observed-row Assumption 7.2 supplies the compact primitive-row
facade for Hansen Theorem 11.4. The error fourth moment is derived from the
observed response/design fourth moments and the linear model. -/
private theorem of_observed_rows
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h72 : SystemObservedResponseFourthMomentConditions μ X e Y β)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hcond : SystemConditionalMeanZero μ Z X e)
    (hSigma : Sigma.PosDef) :
    SURPrimitiveRowGaussianLimitConditions μ Z X e Y Sigma β where
  toSystemPrimitiveRowRegressionMomentConditions :=
    h72.toSystemPrimitiveRowRegressionMomentConditions
  y_aestronglyMeasurable := h72.y_aestronglyMeasurable_at
  conditional_homoskedasticity := hhom
  conditional_mean_zero := hcond
  error_covariance_posDef := hSigma
  linear_model := h72.model
  design_norm_fourth_integrable := h72.design_norm_fourth_integrable
  error_norm_fourth_integrable :=
    h72.error_memLp_four.integrable_norm_pow (by norm_num)

omit [Fintype n] [DecidableEq n] in
/-- The compact primitive-row facade supplies the existing Hansen 11.4
condition package for the feasible SUR estimator. -/
private theorem toGaussianLimitConditions
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURPrimitiveRowGaussianLimitConditions μ Z X e Y Sigma β) :
    SURGaussianLimitConditions μ X e Y Sigma β :=
  of_primitive_row_assumption72_raw_condHomoskedasticity_raw_exog_rowNorm_fourth
      (μ := μ) (Z := Z) h.y_aestronglyMeasurable
      h.toSystemPrimitiveRowRegressionMomentConditions h.conditional_homoskedasticity
      h.conditional_mean_zero h.error_covariance_posDef h.linear_model
      h.design_norm_fourth_integrable h.error_norm_fourth_integrable

omit [Fintype n] [DecidableEq n] in
/-- **Hansen Theorem 11.4**, compact primitive-row facade: the named feasible
SUR estimator has the displayed Gaussian limit. -/
private theorem starObs
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURPrimitiveRowGaussianLimitConditions μ Z X e Y Sigma β) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (surAsymptoticVariance
          (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))) :=
  h.toGaussianLimitConditions.starObs

omit [Fintype n] [DecidableEq n] in
/-- **Hansen Theorem 11.4**, textbook-facing OrZero form of the compact
primitive-row feasible-SUR Gaussian limit. -/
theorem orZeroObs
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURPrimitiveRowGaussianLimitConditions μ Z X e Y Sigma β) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (surAsymptoticVariance
          (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))) := by
  simpa [surBetaEstimatorOrZeroObs_eq_star] using
    h.starObs

omit [Fintype n] [DecidableEq n] in
/-- Gaussian-limit interface form of Hansen Theorem 11.4 under the compact
primitive-row facade. -/
private theorem starGaussianLimit
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURPrimitiveRowGaussianLimitConditions μ Z X e Y Sigma β) :
    GaussianLimit μ
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) :=
  h.toGaussianLimitConditions.starGaussianLimit

omit [Fintype n] [DecidableEq n] in
/-- Gaussian-limit interface form of the textbook-facing OrZero Theorem 11.4
endpoint. -/
private theorem orZeroGaussianLimit
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h : SURPrimitiveRowGaussianLimitConditions μ Z X e Y Sigma β) :
    GaussianLimit μ
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      (surAsymptoticVariance
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹])) := by
  simpa [surBetaEstimatorOrZeroObs_eq_star] using
    h.starGaussianLimit

end SURPrimitiveRowGaussianLimitConditions

omit [Fintype n] [DecidableEq n] in
/-- **Hansen Theorem 11.4** from the literal observed-row Assumption 7.2
surface, conditional mean zero, and the matrix conditional-homoskedasticity
condition `(11.8)`. -/
theorem SURTheorem11_4.orZeroObs_of_observed_rows
    {ζ : Type*} [MeasurableSpace ζ] {Z : Ω → ζ}
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ} {β : k → ℝ}
    (h72 : SystemObservedResponseFourthMomentConditions μ X e Y β)
    (hhom : MatrixSystemConditionalHomoskedasticity μ Z X e Sigma)
    (hcond : SystemConditionalMeanZero μ Z X e)
    (hSigma : Sigma.PosDef) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (surBetaEstimatorOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (surAsymptoticVariance
          (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma⁻¹]))) :=
  (SURPrimitiveRowGaussianLimitConditions.of_observed_rows
    (μ := μ) h72 hhom hcond hSigma).orZeroObs

end HansenEconometrics
