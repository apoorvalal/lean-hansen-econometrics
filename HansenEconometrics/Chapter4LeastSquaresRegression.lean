import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.ProbabilityUtils
import HansenEconometrics.Chapter3Projections

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]

/-- Hansen equation (4.6): OLS equals the true coefficient plus the projected error. -/
@[simp]
theorem olsBeta_linear_decomposition
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBeta X (X *ᵥ β + e) = β + (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ e) := by
  unfold olsBeta
  rw [Matrix.mulVec_add]
  have hxx : Xᵀ *ᵥ (X *ᵥ β) = (Xᵀ * X) *ᵥ β := by
    rw [Matrix.mulVec_mulVec]
  rw [hxx, Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec β (⅟ (Xᵀ * X)) (Xᵀ * X)]
  rw [invOf_mul_self]
  simp

/-- If the model error is orthogonal to the regressors, the closed-form OLS coefficient is `β`. -/
theorem olsBeta_eq_of_regressors_orthogonal_error
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)]
    (he : Xᵀ *ᵥ e = 0) :
    olsBeta X (X *ᵥ β + e) = β := by
  rw [olsBeta_linear_decomposition, he]
  simp

/-- In the finite-sample linear model, fitted values equal signal plus projected error. -/
theorem fitted_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X (X *ᵥ β + e) = X *ᵥ β + hatMatrix X *ᵥ e := by
  unfold fitted
  rw [olsBeta_linear_decomposition, Matrix.mulVec_add]
  rw [← hat_mul_y_eq_closed_form_fit]

/-- In the finite-sample linear model, OLS residuals are the annihilator applied to the error. -/
@[simp]
theorem residual_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n]
    [Invertible (Xᵀ * X)] :
    residual X (X *ᵥ β + e) = annihilatorMatrix X *ᵥ e := by
  unfold residual annihilatorMatrix
  rw [fitted_linear_model, Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Hansen Theorem 4.2 matrix core: conditional covariance formula for OLS. -/
noncomputable def olsConditionalVarianceMatrix
    (X : Matrix n k ℝ) (D : Matrix n n ℝ) [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  ⅟ (Xᵀ * X) * Xᵀ * D * X * ⅟ (Xᵀ * X)

/-- Hansen Section 4.16 infeasible heteroskedastic covariance estimator using the true
squared errors. -/
noncomputable def olsIdealVarianceEstimator
    (X : Matrix n k ℝ) (e : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  olsConditionalVarianceMatrix X (Matrix.diagonal fun i => e i ^ 2)

/-- White's HC0 heteroskedasticity-robust covariance estimator. -/
noncomputable def olsHuberWhiteVarianceEstimator
    (X : Matrix n k ℝ) (y : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  olsConditionalVarianceMatrix X (Matrix.diagonal fun i => residual X y i ^ 2)

/-- HC1 degrees-of-freedom adjustment to the Huber-White covariance estimator. -/
noncomputable def olsHuberWhiteHC1VarianceEstimator
    (X : Matrix n k ℝ) (y : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  ((Fintype.card n : ℝ) / (Fintype.card n - Fintype.card k : ℝ)) •
    olsHuberWhiteVarianceEstimator X y

/-- The covariance formula written as `Aᵀ D A`, where `A = X (XᵀX)⁻¹`. -/
theorem olsConditionalVarianceMatrix_eq_Atranspose_D_A
    (X : Matrix n k ℝ) (D : Matrix n n ℝ) [Invertible (Xᵀ * X)] :
    (X * ⅟ (Xᵀ * X))ᵀ * D * (X * ⅟ (Xᵀ * X)) =
      olsConditionalVarianceMatrix X D := by
  unfold olsConditionalVarianceMatrix
  rw [Matrix.transpose_mul, inv_gram_transpose]
  simp [Matrix.mul_assoc]

/-- Entrywise form of a diagonal covariance sandwich. -/
theorem olsConditionalVarianceMatrix_diagonal_apply
    (X : Matrix n k ℝ) (d : n → ℝ) (a b : k) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsConditionalVarianceMatrix X (Matrix.diagonal d) a b =
      ∑ i, (((⅟ (Xᵀ * X)) * Xᵀ) a i * ((⅟ (Xᵀ * X)) * Xᵀ) b i) * d i := by
  let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
  have hrepr : olsConditionalVarianceMatrix X (Matrix.diagonal d) = w * Matrix.diagonal d * wᵀ := by
    unfold olsConditionalVarianceMatrix
    dsimp [w]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, inv_gram_transpose]
    simp [Matrix.mul_assoc]
  rw [hrepr]
  simp [w, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal, mul_assoc, mul_comm]

/-- Hansen Theorem 4.2 homoskedastic simplification: `D = σ² I`. -/
theorem olsConditionalVarianceMatrix_homoskedastic
    (X : Matrix n k ℝ) (σ2 : ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsConditionalVarianceMatrix X (σ2 • (1 : Matrix n n ℝ)) =
      σ2 • ⅟ (Xᵀ * X) := by
  unfold olsConditionalVarianceMatrix
  rw [Matrix.mul_assoc (⅟ (Xᵀ * X) * Xᵀ) (σ2 • (1 : Matrix n n ℝ)) X]
  simp [Matrix.mul_assoc]

/-- In the linear model, the HC0 estimator can be written using annihilator-transformed errors. -/
theorem olsHuberWhiteVarianceEstimator_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsHuberWhiteVarianceEstimator X (X *ᵥ β + e) =
      olsConditionalVarianceMatrix X
        (Matrix.diagonal fun i => (annihilatorMatrix X *ᵥ e) i ^ 2) := by
  simp [olsHuberWhiteVarianceEstimator]

/-- HC1 is a degrees-of-freedom rescaling of White's HC0 estimator. -/
theorem olsHuberWhiteHC1VarianceEstimator_eq_smul
    (X : Matrix n k ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsHuberWhiteHC1VarianceEstimator X y =
      ((Fintype.card n : ℝ) / (Fintype.card n - Fintype.card k : ℝ)) •
        olsHuberWhiteVarianceEstimator X y := rfl

/-- HC2 covariance estimator: leverage-adjusted by `(1 - hᵢᵢ)⁻¹`.
Lean totalizes `(1 - hᵢᵢ)⁻¹` to `0` at saturated observations
(`hᵢᵢ = 1`); textbook agreement requires `hᵢᵢ < 1`. -/
noncomputable def olsHuberWhiteHC2VarianceEstimator
    (X : Matrix n k ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  olsConditionalVarianceMatrix X
    (Matrix.diagonal fun i => (1 - hatMatrix X i i)⁻¹ * residual X y i ^ 2)

/-- HC3 covariance estimator: leverage-adjusted by `(1 - hᵢᵢ)⁻²`.
Same totalization caveat as HC2 (zero at `hᵢᵢ = 1`). -/
noncomputable def olsHuberWhiteHC3VarianceEstimator
    (X : Matrix n k ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  olsConditionalVarianceMatrix X
    (Matrix.diagonal fun i => ((1 - hatMatrix X i i)⁻¹) ^ 2 * residual X y i ^ 2)

/-- HC leverage-weight ordering on the nonsaturated textbook range.

If a leverage value satisfies `0 ≤ h < 1`, then the HC2 scalar weight
`(1 - h)⁻¹` is at least the HC0 weight `1`, and the HC3 scalar weight
`((1 - h)⁻¹) ^ 2` is at least the HC2 weight. This is the scalar deterministic
core behind finite-sample HC0/HC2/HC3 ordering statements. -/
theorem hc_leverage_weight_ordering {h : ℝ} (h_nonneg : 0 ≤ h) (h_lt_one : h < 1) :
    1 ≤ (1 - h)⁻¹ ∧ (1 - h)⁻¹ ≤ ((1 - h)⁻¹) ^ 2 := by
  have ht_pos : 0 < 1 - h := sub_pos.mpr h_lt_one
  have ht_le_one : 1 - h ≤ 1 := by linarith
  have h_hc2 : 1 ≤ (1 - h)⁻¹ := (one_le_inv₀ ht_pos).2 ht_le_one
  have h_hc3 : (1 - h)⁻¹ ≤ ((1 - h)⁻¹) ^ 2 := by
    simpa [pow_two] using
      (Bound.le_self_pow_of_pos h_hc2 (show 0 < (2 : ℕ) by norm_num))
  exact ⟨h_hc2, h_hc3⟩

/-- Monotone diagonal weights give a positive-semidefinite sandwich difference.

This is the deterministic matrix core behind finite-sample ordering statements
for diagonal covariance estimators such as HC0/HC2/HC3. -/
theorem olsConditionalVarianceMatrix_diagonal_mono_posSemidef
    (X : Matrix n k ℝ) (d₁ d₂ : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hmono : ∀ i, d₁ i ≤ d₂ i) :
    (olsConditionalVarianceMatrix X (Matrix.diagonal d₂) -
      olsConditionalVarianceMatrix X (Matrix.diagonal d₁)).PosSemidef := by
  let A : Matrix n k ℝ := X * ⅟ (Xᵀ * X)
  let D : Matrix n n ℝ := Matrix.diagonal fun i => d₂ i - d₁ i
  have hD : D.PosSemidef := by
    dsimp [D]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hmono i))
  have hpsd : (Aᵀ * D * A).PosSemidef := by
    simpa [A, D, Matrix.conjTranspose] using
      (Matrix.PosSemidef.conjTranspose_mul_mul_same hD A)
  have hdiff :
      olsConditionalVarianceMatrix X (Matrix.diagonal d₂) -
        olsConditionalVarianceMatrix X (Matrix.diagonal d₁) = Aᵀ * D * A := by
    rw [← olsConditionalVarianceMatrix_eq_Atranspose_D_A X (Matrix.diagonal d₂)]
    rw [← olsConditionalVarianceMatrix_eq_Atranspose_D_A X (Matrix.diagonal d₁)]
    dsimp [A, D]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  simpa [hdiff]

/-- Any positive-semidefinite increase in the covariance middle matrix remains
positive semidefinite after the OLS sandwich. -/
theorem olsSandwichMiddle_mono_posSemidef
    (X : Matrix n k ℝ) (M₁ M₂ : Matrix k k ℝ)
    [Invertible (Xᵀ * X)]
    (hmono : (M₂ - M₁).PosSemidef) :
    (⅟ (Xᵀ * X) * M₂ * ⅟ (Xᵀ * X) -
      ⅟ (Xᵀ * X) * M₁ * ⅟ (Xᵀ * X)).PosSemidef := by
  let A : Matrix k k ℝ := ⅟ (Xᵀ * X)
  have hpsd : (Aᵀ * (M₂ - M₁) * A).PosSemidef := by
    simpa [Matrix.conjTranspose] using
      (Matrix.PosSemidef.conjTranspose_mul_mul_same hmono A)
  have hdiff :
      ⅟ (Xᵀ * X) * M₂ * ⅟ (Xᵀ * X) -
        ⅟ (Xᵀ * X) * M₁ * ⅟ (Xᵀ * X) =
          Aᵀ * (M₂ - M₁) * A := by
    dsimp [A]
    rw [inv_gram_transpose]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  rw [hdiff]
  exact hpsd

/-- Matrix-level HC0/HC2 ordering on the nonsaturated leverage range.

If every leverage satisfies `0 ≤ hᵢᵢ < 1`, then the HC2 covariance estimator
dominates HC0 in positive-semidefinite order. -/
theorem olsHuberWhiteVarianceEstimator_le_HC2_posSemidef
    (X : Matrix n k ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hlev_nonneg : ∀ i, 0 ≤ hatMatrix X i i)
    (hlev_lt_one : ∀ i, hatMatrix X i i < 1) :
    (olsHuberWhiteHC2VarianceEstimator X y -
      olsHuberWhiteVarianceEstimator X y).PosSemidef := by
  refine olsConditionalVarianceMatrix_diagonal_mono_posSemidef
    (X := X)
    (d₁ := fun i => residual X y i ^ 2)
    (d₂ := fun i => (1 - hatMatrix X i i)⁻¹ * residual X y i ^ 2)
    ?_
  intro i
  simpa [one_mul] using mul_le_mul_of_nonneg_right
    (hc_leverage_weight_ordering (hlev_nonneg i) (hlev_lt_one i)).1
    (sq_nonneg (residual X y i))

/-- Matrix-level HC2/HC3 ordering on the nonsaturated leverage range.

If every leverage satisfies `0 ≤ hᵢᵢ < 1`, then the HC3 covariance estimator
dominates HC2 in positive-semidefinite order. -/
theorem olsHuberWhiteHC2VarianceEstimator_le_HC3_posSemidef
    (X : Matrix n k ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hlev_nonneg : ∀ i, 0 ≤ hatMatrix X i i)
    (hlev_lt_one : ∀ i, hatMatrix X i i < 1) :
    (olsHuberWhiteHC3VarianceEstimator X y -
      olsHuberWhiteHC2VarianceEstimator X y).PosSemidef := by
  refine olsConditionalVarianceMatrix_diagonal_mono_posSemidef
    (X := X)
    (d₁ := fun i => (1 - hatMatrix X i i)⁻¹ * residual X y i ^ 2)
    (d₂ := fun i => ((1 - hatMatrix X i i)⁻¹) ^ 2 * residual X y i ^ 2)
    ?_
  intro i
  exact mul_le_mul_of_nonneg_right
    (hc_leverage_weight_ordering (hlev_nonneg i) (hlev_lt_one i)).2
    (sq_nonneg (residual X y i))

omit [Fintype k] [DecidableEq k] in
/-- A finite sum of score outer products is positive semidefinite. -/
theorem sum_vecMulVec_posSemidef
    {κ G : Type*} [Finite κ] [Fintype G] (s : G → κ → ℝ) :
    (∑ g, Matrix.vecMulVec (s g) (s g)).PosSemidef := by
  classical
  refine Finset.sum_induction
    (fun g => Matrix.vecMulVec (s g) (s g))
    (fun M : Matrix κ κ ℝ => M.PosSemidef)
    (fun _ _ hA hB => Matrix.PosSemidef.add hA hB)
    Matrix.PosSemidef.zero
    ?_
  intro g _
  simpa using Matrix.posSemidef_vecMulVec_self_star (s g)

/-- Clustered covariance: sandwich on cluster-summed scores. -/
noncomputable def olsClusteredVarianceEstimator
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  let s : G → k → ℝ := fun g a =>
    ∑ i, (if cluster i = g then residual X y i * X i a else 0)
  ⅟ (Xᵀ * X) *
    (∑ g, Matrix.vecMulVec (s g) (s g)) *
    ⅟ (Xᵀ * X)

/-- Hansen equation (4.51): Stata-style finite-sample cluster adjustment
`((n - 1) / (n - k)) * (G / (G - 1))`. -/
noncomputable def clusterFiniteSampleAdjustment
    (n k G : Type*) [Fintype n] [Fintype k] [Fintype G] : ℝ :=
  ((Fintype.card n : ℝ) - 1) / ((Fintype.card n : ℝ) - Fintype.card k) *
    ((Fintype.card G : ℝ) / ((Fintype.card G : ℝ) - 1))

omit [DecidableEq k] in
/-- The clustered finite-sample adjustment is nonnegative on the usual
cardinality range `k < n` and `1 < G`. -/
theorem clusterFiniteSampleAdjustment_nonneg
    {G : Type*} [Fintype G]
    (hnk : Fintype.card k < Fintype.card n)
    (hG : 1 < Fintype.card G) :
    0 ≤ clusterFiniteSampleAdjustment n k G := by
  unfold clusterFiniteSampleAdjustment
  have hnk_real : (Fintype.card k : ℝ) < Fintype.card n := by
    exact_mod_cast hnk
  have hn_pos : (0 : ℝ) < (Fintype.card n : ℝ) - Fintype.card k := by
    linarith
  have hn_ge_one : (1 : ℝ) ≤ Fintype.card n := by
    have hn_nat : 1 ≤ Fintype.card n := by
      exact Nat.succ_le_iff.mpr (lt_of_le_of_lt (Nat.zero_le _) hnk)
    exact_mod_cast hn_nat
  have hn_num_nonneg : 0 ≤ (Fintype.card n : ℝ) - 1 := by
    linarith
  have hG_real : (1 : ℝ) < Fintype.card G := by
    exact_mod_cast hG
  have hG_den_pos : (0 : ℝ) < (Fintype.card G : ℝ) - 1 := by
    linarith
  have hG_num_nonneg : 0 ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast Nat.zero_le (Fintype.card G)
  exact mul_nonneg
    (div_nonneg hn_num_nonneg hn_pos.le)
    (div_nonneg hG_num_nonneg hG_den_pos.le)

/-- Hansen equation (4.50): cluster-robust covariance estimator with the
finite-sample adjustment from equation (4.51). -/
noncomputable def olsClusteredVarianceEstimatorAdjusted
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  clusterFiniteSampleAdjustment n k G • olsClusteredVarianceEstimator X y cluster

/-- The cluster-score middle matrix in the clustered sandwich is positive
semidefinite. -/
theorem olsClusteredScoreMiddle_posSemidef
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [Invertible (Xᵀ * X)] :
    (let s : G → k → ℝ := fun g a =>
        ∑ i, (if cluster i = g then residual X y i * X i a else 0)
      ∑ g, Matrix.vecMulVec (s g) (s g)).PosSemidef := by
  let s : G → k → ℝ := fun g a =>
    ∑ i, (if cluster i = g then residual X y i * X i a else 0)
  simpa [s] using sum_vecMulVec_posSemidef (κ := k) s

/-- The unadjusted clustered sandwich covariance estimator is positive
semidefinite. -/
theorem olsClusteredVarianceEstimator_posSemidef
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    (olsClusteredVarianceEstimator X y cluster).PosSemidef := by
  let s : G → k → ℝ := fun g a =>
    ∑ i, (if cluster i = g then residual X y i * X i a else 0)
  have hmiddle : (∑ g, Matrix.vecMulVec (s g) (s g)).PosSemidef :=
    sum_vecMulVec_posSemidef (κ := k) s
  have hpsd := Matrix.PosSemidef.conjTranspose_mul_mul_same
    hmiddle (⅟ (Xᵀ * X))
  have hinvT : ((Xᵀ * X)⁻¹)ᵀ = (Xᵀ * X)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, gram_transpose]
  simpa [olsClusteredVarianceEstimator, s, Matrix.conjTranspose_eq_transpose_of_trivial,
    hinvT, inv_gram_transpose X, Matrix.mul_assoc] using hpsd

/-- The finite-sample adjusted clustered covariance estimator is positive
semidefinite whenever the adjustment factor is nonnegative. -/
theorem olsClusteredVarianceEstimatorAdjusted_posSemidef
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hadj : 0 ≤ clusterFiniteSampleAdjustment n k G) :
    (olsClusteredVarianceEstimatorAdjusted X y cluster).PosSemidef := by
  simpa [olsClusteredVarianceEstimatorAdjusted] using
    (olsClusteredVarianceEstimator_posSemidef X y cluster).smul hadj

/-- The finite-sample adjusted clustered covariance estimator is positive
semidefinite on the standard cardinality range `k < n` and `1 < G`. -/
theorem olsClusteredVarianceEstimatorAdjusted_posSemidef_of_card
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hnk : Fintype.card k < Fintype.card n)
    (hG : 1 < Fintype.card G) :
    (olsClusteredVarianceEstimatorAdjusted X y cluster).PosSemidef :=
  olsClusteredVarianceEstimatorAdjusted_posSemidef X y cluster
    (clusterFiniteSampleAdjustment_nonneg (n := n) (k := k) hnk hG)

/-- Row index type for observations belonging to cluster `g`. -/
abbrev ClusterIndex {G : Type*} (cluster : n → G) (g : G) :=
  {i : n // cluster i = g}

omit [Fintype k] [DecidableEq k] in
/-- Summing first within clusters and then over clusters is the same as summing
over observations. This is the finite partition identity behind the clustered
block notation. -/
theorem clusterIndex_sum_eq_sum
    {G M : Type*} [Fintype G] [DecidableEq G] [AddCommMonoid M]
    (cluster : n → G) (f : n → M) :
    (∑ g, ∑ i : ClusterIndex cluster g, f i.1) = ∑ i, f i := by
  simpa [ClusterIndex] using (Fintype.sum_fiberwise cluster f)

/-- Cluster-level regressor block `X_g`. -/
def clusterDesign {G : Type*} (X : Matrix n k ℝ) (cluster : n → G) (g : G) :
    Matrix (ClusterIndex cluster g) k ℝ :=
  X.submatrix Subtype.val id

/-- Hansen equation (4.46): the clustered score covariance middle matrix
`Ωₙ = ∑_g X_g' Σ_g X_g`.  The cluster covariance block `Σ_g` is indexed by the
rows belonging to cluster `g`, so the statement supports unequal cluster sizes. -/
noncomputable def clusterCovarianceMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ) :
    Matrix k k ℝ :=
  ∑ g, (clusterDesign X cluster g)ᵀ * Sigma g * clusterDesign X cluster g

/-- Hansen equation (4.47): clustered conditional covariance matrix of the OLS
coefficient, using the clustered middle matrix from equation (4.46). -/
noncomputable def olsClusterConditionalVarianceMatrix
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  ⅟ (Xᵀ * X) * clusterCovarianceMiddle X cluster Sigma * ⅟ (Xᵀ * X)

omit [Fintype k] [DecidableEq k] in
/-- Entrywise form of the clustered covariance middle matrix. -/
theorem clusterCovarianceMiddle_apply
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    (a b : k) :
    clusterCovarianceMiddle X cluster Sigma a b =
      ∑ g, ∑ i, ∑ j, X i.1 a * (X j.1 b * Sigma g i j) := by
  rw [clusterCovarianceMiddle, Matrix.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro g _
  calc
    ((clusterDesign X cluster g)ᵀ * Sigma g * clusterDesign X cluster g) a b =
        ∑ j, (∑ i, X i.1 a * Sigma g i j) * X j.1 b := by
          simp [clusterDesign, Matrix.mul_apply]
    _ = ∑ j, ∑ i, X i.1 a * Sigma g i j * X j.1 b := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, X i.1 a * Sigma g i j * X j.1 b := by
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, X i.1 a * (X j.1 b * Sigma g i j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          ring

omit [Fintype k] [DecidableEq k] in
/-- Positive-semidefinite cluster covariance blocks give a positive-semidefinite
clustered covariance middle matrix. -/
theorem clusterCovarianceMiddle_posSemidef
    [Finite k]
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    (hSigma : ∀ g, (Sigma g).PosSemidef) :
    (clusterCovarianceMiddle X cluster Sigma).PosSemidef := by
  unfold clusterCovarianceMiddle
  refine Finset.sum_induction
    (fun g => (clusterDesign X cluster g)ᵀ * Sigma g * clusterDesign X cluster g)
    (fun M : Matrix k k ℝ => M.PosSemidef)
    (fun _ _ hA hB => Matrix.PosSemidef.add hA hB)
    Matrix.PosSemidef.zero
    ?_
  intro g _
  have hpsd := Matrix.PosSemidef.conjTranspose_mul_mul_same
    (hSigma g) (clusterDesign X cluster g)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hpsd

omit [Fintype k] [DecidableEq k] in
/-- Blockwise positive-semidefinite dominance of cluster covariance blocks is
preserved by Hansen's clustered covariance middle matrix. -/
theorem clusterCovarianceMiddle_mono_posSemidef
    [Finite k]
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G)
    (Sigma₁ Sigma₂ :
      ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    (hSigma : ∀ g, (Sigma₂ g - Sigma₁ g).PosSemidef) :
    (clusterCovarianceMiddle X cluster Sigma₂ -
      clusterCovarianceMiddle X cluster Sigma₁).PosSemidef := by
  have hmiddle :
      (∑ g, (clusterDesign X cluster g)ᵀ * (Sigma₂ g - Sigma₁ g) *
        clusterDesign X cluster g).PosSemidef := by
    refine Finset.sum_induction
      (fun g => (clusterDesign X cluster g)ᵀ * (Sigma₂ g - Sigma₁ g) *
        clusterDesign X cluster g)
      (fun M : Matrix k k ℝ => M.PosSemidef)
      (fun _ _ hA hB => Matrix.PosSemidef.add hA hB)
      Matrix.PosSemidef.zero
      ?_
    intro g _
    have hpsd := Matrix.PosSemidef.conjTranspose_mul_mul_same
      (hSigma g) (clusterDesign X cluster g)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using hpsd
  have hdiff :
      clusterCovarianceMiddle X cluster Sigma₂ -
        clusterCovarianceMiddle X cluster Sigma₁ =
        ∑ g, (clusterDesign X cluster g)ᵀ * (Sigma₂ g - Sigma₁ g) *
          clusterDesign X cluster g := by
    rw [clusterCovarianceMiddle, clusterCovarianceMiddle, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro g _
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  simpa [hdiff] using hmiddle

/-- Positive-semidefinite cluster covariance blocks give a positive-semidefinite
clustered OLS covariance sandwich. -/
theorem olsClusterConditionalVarianceMatrix_posSemidef
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    [Invertible (Xᵀ * X)]
    (hSigma : ∀ g, (Sigma g).PosSemidef) :
    (olsClusterConditionalVarianceMatrix X cluster Sigma).PosSemidef := by
  have hmiddle := clusterCovarianceMiddle_posSemidef X cluster Sigma hSigma
  have hpsd := Matrix.PosSemidef.conjTranspose_mul_mul_same
    hmiddle (⅟ (Xᵀ * X))
  have hinvT : ((Xᵀ * X)⁻¹)ᵀ = (Xᵀ * X)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, gram_transpose]
  simpa [olsClusterConditionalVarianceMatrix,
    Matrix.conjTranspose_eq_transpose_of_trivial, hinvT, Matrix.mul_assoc]
    using hpsd

/-- Blockwise positive-semidefinite dominance of cluster covariance blocks is
preserved by the clustered OLS covariance sandwich. -/
theorem olsClusterConditionalVarianceMatrix_mono_posSemidef
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G)
    (Sigma₁ Sigma₂ :
      ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    [Invertible (Xᵀ * X)]
    (hSigma : ∀ g, (Sigma₂ g - Sigma₁ g).PosSemidef) :
    (olsClusterConditionalVarianceMatrix X cluster Sigma₂ -
      olsClusterConditionalVarianceMatrix X cluster Sigma₁).PosSemidef := by
  simpa [olsClusterConditionalVarianceMatrix] using
    olsSandwichMiddle_mono_posSemidef
      (X := X)
      (M₁ := clusterCovarianceMiddle X cluster Sigma₁)
      (M₂ := clusterCovarianceMiddle X cluster Sigma₂)
      (clusterCovarianceMiddle_mono_posSemidef X cluster Sigma₁ Sigma₂ hSigma)

omit [Fintype k] [DecidableEq k] in
/-- A block outer-product middle matrix can be rewritten as a sum of cluster
score outer products.  This is the deterministic algebra behind the three
equivalent expressions in Hansen equation (4.49). -/
theorem clusterCovarianceMiddle_outer_eq_scoreMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G)
    (u : ∀ g, ClusterIndex cluster g → ℝ) :
    clusterCovarianceMiddle X cluster (fun g => Matrix.vecMulVec (u g) (u g)) =
      ∑ g, Matrix.vecMulVec ((clusterDesign X cluster g)ᵀ *ᵥ u g)
        ((clusterDesign X cluster g)ᵀ *ᵥ u g) := by
  unfold clusterCovarianceMiddle
  refine Finset.sum_congr rfl ?_
  intro g _
  let C : Matrix (ClusterIndex cluster g) k ℝ := clusterDesign X cluster g
  have hvec : (u g) ᵥ* C = Cᵀ *ᵥ u g := by
    exact (Matrix.mulVec_transpose C (u g)).symm
  calc
    (clusterDesign X cluster g)ᵀ * Matrix.vecMulVec (u g) (u g) *
        clusterDesign X cluster g =
        Cᵀ * Matrix.vecMulVec (u g) (u g) * C := rfl
    _ = Matrix.vecMulVec (Cᵀ *ᵥ u g) (u g) * C := by
          rw [Matrix.mul_vecMulVec]
    _ = Matrix.vecMulVec (Cᵀ *ᵥ u g) ((u g) ᵥ* C) := by
          rw [Matrix.vecMulVec_mul]
    _ = Matrix.vecMulVec ((clusterDesign X cluster g)ᵀ *ᵥ u g)
          ((clusterDesign X cluster g)ᵀ *ᵥ u g) := by
          rw [hvec]

/-- Cluster-level full-sample OLS residual block `e_hat_g`. -/
noncomputable def clusterResidual
    {G : Type*} (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [Invertible (Xᵀ * X)] : ClusterIndex cluster g → ℝ :=
  fun i => residual X y i

/-- Cluster leverage block `X_g (X'X)^{-1} X_g'`. -/
noncomputable def clusterLeverageBlock
    {G : Type*} (X : Matrix n k ℝ) (cluster : n → G) (g : G)
    [Invertible (Xᵀ * X)] : Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ :=
  clusterDesign X cluster g * ⅟ (Xᵀ * X) * (clusterDesign X cluster g)ᵀ

/-- Hansen equation (4.52) adjustment matrix, `I_g - X_g (X'X)^{-1} X_g'`. -/
noncomputable def clusterLeaveOutAdjustmentMatrix
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ :=
  1 - clusterLeverageBlock X cluster g

/-- Hansen equation (4.52): CR3-style cluster prediction errors
`tilde e_g = (I_g - X_g (X'X)^{-1} X_g')^{-1} e_hat_g`. -/
noncomputable def clusterCR3Residual
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    [Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)] :
    ClusterIndex cluster g → ℝ :=
  ⅟ (clusterLeaveOutAdjustmentMatrix X cluster g) *ᵥ
    clusterResidual X y cluster g

/-- The CR3 residual solves the cluster adjustment equation
`(I_g - X_g (X'X)^{-1} X_g') \tilde e_g = \hat e_g`. -/
theorem clusterLeaveOutAdjustmentMatrix_mulVec_clusterCR3Residual
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    [Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)] :
    clusterLeaveOutAdjustmentMatrix X cluster g *ᵥ
      clusterCR3Residual X y cluster g =
        clusterResidual X y cluster g := by
  unfold clusterCR3Residual
  rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]

/-- Cluster-level response block `Y_g`. -/
def clusterResponse {G : Type*} (y : n → ℝ) (cluster : n → G) (g : G) :
    ClusterIndex cluster g → ℝ :=
  fun i => y i

/-- Cluster-level model error block `e_g`. -/
def clusterError {G : Type*} (e : n → ℝ) (cluster : n → G) (g : G) :
    ClusterIndex cluster g → ℝ :=
  fun i => e i

/-- Cluster contribution `X_g'X_g` to the full Gram matrix. -/
noncomputable def clusterGramContribution
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (cluster : n → G) (g : G) :
    Matrix k k ℝ :=
  (clusterDesign X cluster g)ᵀ * clusterDesign X cluster g

/-- Cluster contribution `X_g'Y_g` to the full cross product. -/
noncomputable def clusterCrossContribution
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G) :
    k → ℝ :=
  (clusterDesign X cluster g)ᵀ *ᵥ clusterResponse y cluster g

/-- Cluster score `X_g'e_g` for the true model errors. -/
noncomputable def clusterErrorScore
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (e : n → ℝ) (cluster : n → G)
    (g : G) : k → ℝ :=
  (clusterDesign X cluster g)ᵀ *ᵥ clusterError e cluster g

omit [Fintype k] [DecidableEq k] in
/-- Entrywise form of the cluster Gram contribution. -/
theorem clusterGramContribution_apply
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (cluster : n → G) (g : G)
    (a b : k) :
    clusterGramContribution X cluster g a b =
      ∑ i : ClusterIndex cluster g, X i.1 a * X i.1 b := by
  simp [clusterGramContribution, clusterDesign, Matrix.mul_apply]

omit [Fintype k] [DecidableEq k] in
/-- Entrywise form of the cluster cross-product contribution. -/
theorem clusterCrossContribution_apply
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    (a : k) :
    clusterCrossContribution X y cluster g a =
      ∑ i : ClusterIndex cluster g, X i.1 a * y i.1 := by
  simp [clusterCrossContribution, clusterDesign, clusterResponse, Matrix.mulVec, dotProduct]

omit [Fintype k] [DecidableEq k] in
/-- Entrywise form of the true-error cluster score. -/
theorem clusterErrorScore_apply
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (e : n → ℝ) (cluster : n → G)
    (g : G) (a : k) :
    clusterErrorScore X e cluster g a =
      ∑ i : ClusterIndex cluster g, X i.1 a * e i.1 := by
  simp [clusterErrorScore, clusterDesign, clusterError, Matrix.mulVec, dotProduct]

omit [Fintype k] [DecidableEq k] in
/-- The cluster Gram contributions add back to the full Gram matrix `X'X`. -/
theorem sum_clusterGramContribution_eq_gram
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (cluster : n → G) :
    (∑ g, clusterGramContribution X cluster g) = Xᵀ * X := by
  ext a b
  calc
    (∑ g, clusterGramContribution X cluster g) a b =
        ∑ g, ∑ i : ClusterIndex cluster g, X i.1 a * X i.1 b := by
          rw [Matrix.sum_apply]
          exact Finset.sum_congr rfl fun g _ =>
            clusterGramContribution_apply X cluster g a b
    _ = ∑ i, X i a * X i b := by
          simpa using
            (clusterIndex_sum_eq_sum (cluster := cluster)
              (f := fun i => X i a * X i b))
    _ = (Xᵀ * X) a b := by
          simp [Matrix.mul_apply, Matrix.transpose_apply]

omit [Fintype k] [DecidableEq k] in
/-- The cluster cross-product contributions add back to the full cross product
`X'Y`. -/
theorem sum_clusterCrossContribution_eq_cross
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) :
    (∑ g, clusterCrossContribution X y cluster g) = Xᵀ *ᵥ y := by
  ext a
  calc
    (∑ g, clusterCrossContribution X y cluster g) a =
        ∑ g, ∑ i : ClusterIndex cluster g, X i.1 a * y i.1 := by
          simp [clusterCrossContribution_apply]
    _ = ∑ i, X i a * y i := by
          simpa using
            (clusterIndex_sum_eq_sum (cluster := cluster)
              (f := fun i => X i a * y i))
    _ = (Xᵀ *ᵥ y) a := by
          simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

omit [Fintype k] [DecidableEq k] in
/-- The true-error cluster scores add back to `X'e`. -/
theorem sum_clusterErrorScore_eq_transpose_mulVec_error
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (e : n → ℝ) (cluster : n → G) :
    (∑ g, clusterErrorScore X e cluster g) = Xᵀ *ᵥ e := by
  ext a
  calc
    (∑ g, clusterErrorScore X e cluster g) a =
        ∑ g, ∑ i : ClusterIndex cluster g, X i.1 a * e i.1 := by
          simp [clusterErrorScore_apply, Finset.sum_apply]
    _ = ∑ i, X i a * e i := by
          simpa using
            (clusterIndex_sum_eq_sum (cluster := cluster)
              (f := fun i => X i a * e i))
    _ = (Xᵀ *ᵥ e) a := by
          simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- Hansen clustered OLS decomposition:
`β_hat - β = (X'X)^{-1} ∑_g X_g'e_g`. -/
theorem olsBeta_linear_decomposition_clusterScores
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (cluster : n → G)
    [Invertible (Xᵀ * X)] :
    olsBeta X (X *ᵥ β + e) =
      β + ⅟ (Xᵀ * X) *ᵥ (∑ g, clusterErrorScore X e cluster g) := by
  rw [olsBeta_linear_decomposition]
  rw [sum_clusterErrorScore_eq_transpose_mulVec_error]

omit [Fintype k] [DecidableEq k] in
/-- The infeasible true-error block outer-product middle matrix is the same
object as the true-error cluster-score middle matrix. -/
theorem clusterCovarianceMiddle_errorOuter_eq_clusterErrorScoreMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (e : n → ℝ) (cluster : n → G) :
    clusterCovarianceMiddle X cluster
        (fun g => Matrix.vecMulVec (clusterError e cluster g)
          (clusterError e cluster g)) =
      ∑ g, Matrix.vecMulVec (clusterErrorScore X e cluster g)
        (clusterErrorScore X e cluster g) := by
  simpa [clusterErrorScore] using
    (clusterCovarianceMiddle_outer_eq_scoreMiddle
      (X := X) (cluster := cluster)
      (u := fun g => clusterError e cluster g))

/-- Cluster score `X_g' \hat e_g` for the full-sample OLS residuals. -/
noncomputable def clusterScore
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [Invertible (Xᵀ * X)] : k → ℝ :=
  (clusterDesign X cluster g)ᵀ *ᵥ clusterResidual X y cluster g

/-- Entrywise form of the full-sample residual cluster score. -/
theorem clusterScore_apply
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [Invertible (Xᵀ * X)] (a : k) :
    clusterScore X y cluster g a =
      ∑ i : ClusterIndex cluster g, X i.1 a * residual X y i.1 := by
  simp [clusterScore, clusterDesign, clusterResidual, Matrix.mulVec, dotProduct]

/-- The named cluster score agrees with the indicator-sum score used in the
clustered sandwich definition. -/
theorem clusterScore_eq_indicator_sum
    {G : Type*} [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [Invertible (Xᵀ * X)] :
    clusterScore X y cluster g =
      fun a => ∑ i, (if cluster i = g then residual X y i * X i a else 0) := by
  ext a
  rw [clusterScore_apply]
  calc
    (∑ i : ClusterIndex cluster g, X i.1 a * residual X y i.1) =
        ∑ i : ClusterIndex cluster g, residual X y i.1 * X i.1 a := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = ∑ i : n, (if cluster i = g then residual X y i * X i a else 0) := by
          let f : n → ℝ := fun i => residual X y i * X i a
          have hsub :
              (∑ i ∈ Finset.univ.filter (fun i : n => cluster i = g), f i) =
                ∑ i : ClusterIndex cluster g, f i.1 := by
            refine Finset.sum_subtype
              (Finset.univ.filter (fun i : n => cluster i = g)) ?_ f
            intro i
            simp
          have hfilter :
              (∑ i ∈ Finset.univ.filter (fun i : n => cluster i = g), f i) =
                ∑ i : n, (if cluster i = g then f i else 0) := by
            simpa using
              (Finset.sum_filter
                (s := Finset.univ) (p := fun i : n => cluster i = g) (f := f))
          simpa [f] using hsub.symm.trans hfilter

/-- Clustered sandwich covariance written with the named residual cluster-score
API. -/
theorem olsClusteredVarianceEstimator_eq_clusterScore
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsClusteredVarianceEstimator X y cluster =
      ⅟ (Xᵀ * X) *
        (∑ g, Matrix.vecMulVec (clusterScore X y cluster g) (clusterScore X y cluster g)) *
        ⅟ (Xᵀ * X) := by
  unfold olsClusteredVarianceEstimator
  simp_rw [clusterScore_eq_indicator_sum]

/-- The full-sample residual cluster scores add back to `X'\hat e`. -/
theorem sum_clusterScore_eq_transpose_mulVec_residual
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [Invertible (Xᵀ * X)] :
    (∑ g, clusterScore X y cluster g) = Xᵀ *ᵥ residual X y := by
  ext a
  calc
    (∑ g, clusterScore X y cluster g) a =
        ∑ g, ∑ i : ClusterIndex cluster g, X i.1 a * residual X y i.1 := by
          simp [clusterScore_apply, Finset.sum_apply]
    _ = ∑ i, X i a * residual X y i := by
          simpa using
            (clusterIndex_sum_eq_sum (cluster := cluster)
              (f := fun i => X i a * residual X y i))
    _ = (Xᵀ *ᵥ residual X y) a := by
          simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- The residual cluster scores sum to zero by the OLS normal equations. -/
theorem sum_clusterScore_eq_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [Invertible (Xᵀ * X)] :
    (∑ g, clusterScore X y cluster g) = 0 := by
  rw [sum_clusterScore_eq_transpose_mulVec_residual]
  exact normal_equations X y

/-- The residual block outer-product middle matrix is the same object as the
cluster-score middle matrix in the Arellano estimator. -/
theorem clusterCovarianceMiddle_residualOuter_eq_clusterScoreMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [Invertible (Xᵀ * X)] :
    clusterCovarianceMiddle X cluster
        (fun g => Matrix.vecMulVec (clusterResidual X y cluster g)
          (clusterResidual X y cluster g)) =
      ∑ g, Matrix.vecMulVec (clusterScore X y cluster g)
        (clusterScore X y cluster g) := by
  simpa [clusterScore] using
    (clusterCovarianceMiddle_outer_eq_scoreMiddle
      (X := X) (cluster := cluster)
      (u := fun g => clusterResidual X y cluster g))

/-- Hansen equation (4.50) with the residual block outer-product expression
for `Ω_hat_n`. -/
theorem olsClusteredVarianceEstimator_eq_clusterCovarianceMiddle_residualOuter
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsClusteredVarianceEstimator X y cluster =
      ⅟ (Xᵀ * X) *
        clusterCovarianceMiddle X cluster
          (fun g => Matrix.vecMulVec (clusterResidual X y cluster g)
            (clusterResidual X y cluster g)) *
        ⅟ (Xᵀ * X) := by
  rw [olsClusteredVarianceEstimator_eq_clusterScore]
  rw [clusterCovarianceMiddle_residualOuter_eq_clusterScoreMiddle]

/-- Reduced Gram matrix after removing cluster `g`, written as
`X'X - X_g'X_g`. -/
noncomputable def clusterLeaveOutGram
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (cluster : n → G) (g : G) :
    Matrix k k ℝ :=
  Xᵀ * X - clusterGramContribution X cluster g

/-- Reduced cross product after removing cluster `g`, written as
`X'Y - X_g'Y_g`. -/
noncomputable def clusterLeaveOutCross
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G) :
    k → ℝ :=
  Xᵀ *ᵥ y - clusterCrossContribution X y cluster g

/-- Cluster leave-out coefficient computed from the reduced Gram/cross products. -/
noncomputable def clusterLeaveOutBeta
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [Invertible (clusterLeaveOutGram X cluster g)] : k → ℝ :=
  ⅟ (clusterLeaveOutGram X cluster g) *ᵥ
    clusterLeaveOutCross X y cluster g

/-- The reduced cluster coefficient satisfies the reduced normal equations. -/
theorem clusterLeaveOutGram_mulVec_clusterLeaveOutBeta
    {G : Type*} [DecidableEq G] (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [Invertible (clusterLeaveOutGram X cluster g)] :
    clusterLeaveOutGram X cluster g *ᵥ clusterLeaveOutBeta X y cluster g =
      clusterLeaveOutCross X y cluster g := by
  unfold clusterLeaveOutBeta
  rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]

/-- Cluster residuals are the cluster response minus fitted values from the
full-sample coefficient. -/
theorem clusterResidual_eq_response_sub_design_mulVec_olsBeta
    {G : Type*} (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [Invertible (Xᵀ * X)] :
    clusterResidual X y cluster g =
      clusterResponse y cluster g - clusterDesign X cluster g *ᵥ olsBeta X y := by
  ext i
  simp [clusterResidual, clusterResponse, clusterDesign, residual, fitted, Matrix.mulVec,
    dotProduct]

/-- Cluster cross product decomposes into fitted and residual cluster pieces. -/
theorem clusterCrossContribution_eq_gram_mul_olsBeta_add_residual
    {G : Type*} [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [Invertible (Xᵀ * X)] :
    clusterCrossContribution X y cluster g =
      clusterGramContribution X cluster g *ᵥ olsBeta X y +
        (clusterDesign X cluster g)ᵀ *ᵥ clusterResidual X y cluster g := by
  let C : Matrix (ClusterIndex cluster g) k ℝ := clusterDesign X cluster g
  have hres := clusterResidual_eq_response_sub_design_mulVec_olsBeta X y cluster g
  have hy : clusterResponse y cluster g = C *ᵥ olsBeta X y + clusterResidual X y cluster g := by
    rw [hres]
    ext i
    simp [C]
  unfold clusterCrossContribution clusterGramContribution
  rw [hy, Matrix.mulVec_add, Matrix.mulVec_mulVec]

/-- Applying `X_g'` to the CR3 adjustment equation gives the residual cluster
cross product in terms of the adjusted CR3 residuals. -/
theorem clusterDesign_transpose_mulVec_clusterResidual_eq_cr3
    {G : Type*} [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    [Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)] :
    (clusterDesign X cluster g)ᵀ *ᵥ clusterResidual X y cluster g =
      (clusterDesign X cluster g)ᵀ *ᵥ clusterCR3Residual X y cluster g -
        clusterGramContribution X cluster g *ᵥ
          (⅟ (Xᵀ * X) *ᵥ
            ((clusterDesign X cluster g)ᵀ *ᵥ clusterCR3Residual X y cluster g)) := by
  let C : Matrix (ClusterIndex cluster g) k ℝ := clusterDesign X cluster g
  let u : ClusterIndex cluster g → ℝ := clusterCR3Residual X y cluster g
  have h := congrArg (fun v => Cᵀ *ᵥ v)
    (clusterLeaveOutAdjustmentMatrix_mulVec_clusterCR3Residual X y cluster g)
  dsimp [C, u] at h
  rw [clusterLeaveOutAdjustmentMatrix, clusterLeverageBlock, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_sub] at h
  simpa [clusterGramContribution, C, Matrix.mulVec_mulVec, Matrix.mul_assoc] using h.symm

/-- Hansen equation (4.53), reduced-Gram form.

The cluster-deleted coefficient equals the full-sample coefficient minus the
cluster leverage correction based on the CR3-style prediction errors. -/
theorem clusterLeaveOutBeta_eq_olsBeta_sub_invGram_mulVec_cr3Residual
    {G : Type*} [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    [Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)]
    [Invertible (clusterLeaveOutGram X cluster g)] :
    clusterLeaveOutBeta X y cluster g =
      olsBeta X y -
        ⅟ (Xᵀ * X) *ᵥ
          ((clusterDesign X cluster g)ᵀ *ᵥ clusterCR3Residual X y cluster g) := by
  let C : Matrix (ClusterIndex cluster g) k ℝ := clusterDesign X cluster g
  let u : ClusterIndex cluster g → ℝ := clusterCR3Residual X y cluster g
  let d : k → ℝ := ⅟ (Xᵀ * X) *ᵥ (Cᵀ *ᵥ u)
  let β : k → ℝ := olsBeta X y
  have hfull : (Xᵀ * X) *ᵥ β = Xᵀ *ᵥ y := by
    dsimp [β]
    unfold olsBeta
    rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]
  have hd : (Xᵀ * X) *ᵥ d = Cᵀ *ᵥ u := by
    dsimp [d]
    rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]
  have hres := clusterDesign_transpose_mulVec_clusterResidual_eq_cr3
    (X := X) (y := y) (cluster := cluster) (g := g)
  have hcross := clusterCrossContribution_eq_gram_mul_olsBeta_add_residual
    (X := X) (y := y) (cluster := cluster) (g := g)
  have hnormal :
      clusterLeaveOutGram X cluster g *ᵥ (β - d) =
        clusterLeaveOutCross X y cluster g := by
    calc
      clusterLeaveOutGram X cluster g *ᵥ (β - d) =
          (Xᵀ * X) *ᵥ β - clusterGramContribution X cluster g *ᵥ β -
            ((Xᵀ * X) *ᵥ d - clusterGramContribution X cluster g *ᵥ d) := by
            ext a
            simp [clusterLeaveOutGram, Matrix.sub_mulVec, Matrix.mulVec_sub]
      _ = Xᵀ *ᵥ y -
            (clusterGramContribution X cluster g *ᵥ β +
              ((clusterDesign X cluster g)ᵀ *ᵥ u -
                clusterGramContribution X cluster g *ᵥ d)) := by
            rw [hfull, hd]
            ext a
            simp
            abel
      _ = Xᵀ *ᵥ y - clusterCrossContribution X y cluster g := by
            rw [hcross, hres]
      _ = clusterLeaveOutCross X y cluster g := by
            simp [clusterLeaveOutCross]
  calc
    clusterLeaveOutBeta X y cluster g =
        ⅟ (clusterLeaveOutGram X cluster g) *ᵥ
          clusterLeaveOutCross X y cluster g := rfl
    _ = ⅟ (clusterLeaveOutGram X cluster g) *ᵥ
          (clusterLeaveOutGram X cluster g *ᵥ (β - d)) := by
          rw [hnormal]
    _ = β - d := by
          rw [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec]

/-- CR3 cluster score `X_g' \tilde e_g`. -/
noncomputable def clusterCR3Score
    {G : Type*} [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    [Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)] : k → ℝ :=
  (clusterDesign X cluster g)ᵀ *ᵥ clusterCR3Residual X y cluster g

/-- Entrywise form of the CR3 cluster score. -/
theorem clusterCR3Score_apply
    {G : Type*} [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    [Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)] (a : k) :
    clusterCR3Score X y cluster g a =
      ∑ i : ClusterIndex cluster g, X i.1 a * clusterCR3Residual X y cluster g i := by
  simp [clusterCR3Score, clusterDesign, Matrix.mulVec, dotProduct]

/-- Hansen equation (4.54): CR3-style cluster-robust covariance estimator using
leave-cluster-out prediction errors. -/
noncomputable def olsClusteredCR3VarianceEstimator
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)) :
    Matrix k k ℝ :=
  let s : G → k → ℝ := fun g a =>
    letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
    ∑ i : ClusterIndex cluster g, X i.1 a * clusterCR3Residual X y cluster g i
  ⅟ (Xᵀ * X) *
    (∑ g, Matrix.vecMulVec (s g) (s g)) *
    ⅟ (Xᵀ * X)

/-- CR3 cluster-score middle matrix, `∑_g (X_g' \tilde e_g)(X_g' \tilde e_g)'`. -/
noncomputable def clusterCR3ScoreMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)) :
    Matrix k k ℝ :=
  ∑ g,
    letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
    Matrix.vecMulVec (clusterCR3Score X y cluster g)
      (clusterCR3Score X y cluster g)

/-- The CR3 clustered sandwich written with the named CR3 cluster-score API. -/
theorem olsClusteredCR3VarianceEstimator_eq_clusterCR3Score
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)) :
    olsClusteredCR3VarianceEstimator X y cluster hInv =
      ⅟ (Xᵀ * X) *
        (∑ g,
          letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
          Matrix.vecMulVec (clusterCR3Score X y cluster g)
            (clusterCR3Score X y cluster g)) *
        ⅟ (Xᵀ * X) := by
  unfold olsClusteredCR3VarianceEstimator
  apply congrArg (fun M => ⅟ (Xᵀ * X) * M * ⅟ (Xᵀ * X))
  refine Finset.sum_congr rfl ?_
  intro g _
  letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
  have hscore :
      (fun a : k =>
        ∑ i : ClusterIndex cluster g, X i.1 a * clusterCR3Residual X y cluster g i) =
          clusterCR3Score X y cluster g := by
    ext a
    exact (clusterCR3Score_apply X y cluster g a).symm
  simp [hscore]

/-- The CR3 clustered sandwich written through the named CR3 score-middle matrix. -/
theorem olsClusteredCR3VarianceEstimator_eq_clusterCR3ScoreMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)) :
    olsClusteredCR3VarianceEstimator X y cluster hInv =
      ⅟ (Xᵀ * X) * clusterCR3ScoreMiddle X y cluster hInv * ⅟ (Xᵀ * X) := by
  simpa [clusterCR3ScoreMiddle] using
    olsClusteredCR3VarianceEstimator_eq_clusterCR3Score X y cluster hInv

/-- The CR3 block outer-product middle matrix is the same object as the
CR3 cluster-score middle matrix. -/
theorem clusterCovarianceMiddle_cr3Outer_eq_clusterCR3ScoreMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)) :
    clusterCovarianceMiddle X cluster
        (fun g =>
          letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
          Matrix.vecMulVec (clusterCR3Residual X y cluster g)
            (clusterCR3Residual X y cluster g)) =
      ∑ g,
        letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
        Matrix.vecMulVec (clusterCR3Score X y cluster g)
          (clusterCR3Score X y cluster g) := by
  simpa [clusterCR3Score] using
    (clusterCovarianceMiddle_outer_eq_scoreMiddle
      (X := X) (cluster := cluster)
      (u := fun g =>
        letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
        clusterCR3Residual X y cluster g))

/-- Hansen equation (4.54) with the CR3 residual block outer-product expression
for the clustered middle matrix. -/
theorem olsClusteredCR3VarianceEstimator_eq_clusterCovarianceMiddle_cr3Outer
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)) :
    olsClusteredCR3VarianceEstimator X y cluster hInv =
      ⅟ (Xᵀ * X) *
        clusterCovarianceMiddle X cluster
          (fun g =>
            letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
            Matrix.vecMulVec (clusterCR3Residual X y cluster g)
              (clusterCR3Residual X y cluster g)) *
        ⅟ (Xᵀ * X) := by
  rw [olsClusteredCR3VarianceEstimator_eq_clusterCR3Score]
  rw [clusterCovarianceMiddle_cr3Outer_eq_clusterCR3ScoreMiddle]

/-- CR3 conservativeness bridge. If the CR3 cluster-score middle matrix
dominates a target middle matrix in positive-semidefinite order, then the full
CR3 sandwich dominates the corresponding target sandwich. -/
theorem olsClusteredCR3VarianceEstimator_conservative_of_middle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g))
    (M : Matrix k k ℝ)
    (hmiddle :
      ((∑ g,
          letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
          Matrix.vecMulVec (clusterCR3Score X y cluster g)
            (clusterCR3Score X y cluster g)) - M).PosSemidef) :
    (olsClusteredCR3VarianceEstimator X y cluster hInv -
      ⅟ (Xᵀ * X) * M * ⅟ (Xᵀ * X)).PosSemidef := by
  rw [olsClusteredCR3VarianceEstimator_eq_clusterCR3Score]
  exact olsSandwichMiddle_mono_posSemidef
    (X := X)
    (M₁ := M)
    (M₂ := ∑ g,
      letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
      Matrix.vecMulVec (clusterCR3Score X y cluster g)
        (clusterCR3Score X y cluster g))
    hmiddle

/-- The CR3-style clustered covariance estimator is positive semidefinite. -/
theorem olsClusteredCR3VarianceEstimator_posSemidef
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)) :
    (olsClusteredCR3VarianceEstimator X y cluster hInv).PosSemidef := by
  let s : G → k → ℝ := fun g a =>
    letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
    ∑ i : ClusterIndex cluster g, X i.1 a * clusterCR3Residual X y cluster g i
  have hmiddle : (∑ g, Matrix.vecMulVec (s g) (s g)).PosSemidef :=
    sum_vecMulVec_posSemidef (κ := k) s
  have hpsd := Matrix.PosSemidef.conjTranspose_mul_mul_same
    hmiddle (⅟ (Xᵀ * X))
  have hinvT : ((Xᵀ * X)⁻¹)ᵀ = (Xᵀ * X)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, gram_transpose]
  simpa [olsClusteredCR3VarianceEstimator, s, Matrix.conjTranspose_eq_transpose_of_trivial,
    hinvT, inv_gram_transpose X, Matrix.mul_assoc] using hpsd

omit [DecidableEq k] in
/-- When every observation is its own cluster, Hansen's finite-sample cluster
adjustment reduces to the HC1 degrees-of-freedom adjustment. -/
theorem clusterFiniteSampleAdjustment_singleton
    (hcard : 1 < Fintype.card n) :
    clusterFiniteSampleAdjustment n k n =
      (Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - Fintype.card k) := by
  unfold clusterFiniteSampleAdjustment
  have hn_minus_one_ne_zero : (Fintype.card n : ℝ) - 1 ≠ 0 := by
    have hcard_real : (1 : ℝ) < Fintype.card n := by exact_mod_cast hcard
    linarith
  by_cases hden : (Fintype.card n : ℝ) - Fintype.card k = 0
  · simp [hden]
  · field_simp [hn_minus_one_ne_zero, hden]

/-- Singleton clusters reduce the clustered sandwich to HC0. -/
theorem olsClusteredVarianceEstimator_singleton
    (X : Matrix n k ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsClusteredVarianceEstimator X y (fun i : n => i) =
      olsHuberWhiteVarianceEstimator X y := by
  have hmiddle :
      (∑ g, Matrix.vecMulVec
        (fun a : k => ∑ i, (if i = g then residual X y i * X i a else 0))
        (fun a : k => ∑ i, (if i = g then residual X y i * X i a else 0))) =
        Xᵀ * Matrix.diagonal (fun i => residual X y i ^ 2) * X := by
    ext a b
    calc
      (∑ g, Matrix.vecMulVec
        (fun a : k => ∑ i, (if i = g then residual X y i * X i a else 0))
        (fun a : k => ∑ i, (if i = g then residual X y i * X i a else 0))) a b =
          ∑ g, (residual X y g * X g a) * (residual X y g * X g b) := by
            rw [Matrix.sum_apply]
            simp [Matrix.vecMulVec_apply]
      _ = ∑ g, X g a * residual X y g ^ 2 * X g b := by
            refine Finset.sum_congr rfl ?_
            intro g _
            ring
      _ = (Xᵀ * Matrix.diagonal (fun i => residual X y i ^ 2) * X) a b := by
            simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal, mul_left_comm,
              mul_comm]
  unfold olsClusteredVarianceEstimator olsHuberWhiteVarianceEstimator olsConditionalVarianceMatrix
  change ⅟ (Xᵀ * X) *
      (∑ g, Matrix.vecMulVec
        (fun a : k => ∑ i, (if i = g then residual X y i * X i a else 0))
        (fun a : k => ∑ i, (if i = g then residual X y i * X i a else 0))) *
        ⅟ (Xᵀ * X) =
      ⅟ (Xᵀ * X) * Xᵀ * Matrix.diagonal (fun i => residual X y i ^ 2) * X *
        ⅟ (Xᵀ * X)
  rw [hmiddle]
  simp [Matrix.mul_assoc]

/-- With singleton clusters, the finite-sample adjusted clustered estimator is
exactly HC1. -/
theorem olsClusteredVarianceEstimatorAdjusted_singleton
    (X : Matrix n k ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hcard : 1 < Fintype.card n) :
    olsClusteredVarianceEstimatorAdjusted X y (fun i : n => i) =
      olsHuberWhiteHC1VarianceEstimator X y := by
  unfold olsClusteredVarianceEstimatorAdjusted olsHuberWhiteHC1VarianceEstimator
  rw [olsClusteredVarianceEstimator_singleton]
  rw [clusterFiniteSampleAdjustment_singleton (n := n) (k := k) hcard]

/-- In the linear model, HC2 uses annihilator-transformed errors. -/
theorem olsHuberWhiteHC2VarianceEstimator_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsHuberWhiteHC2VarianceEstimator X (X *ᵥ β + e) =
      olsConditionalVarianceMatrix X
        (Matrix.diagonal fun i =>
          (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e) i ^ 2) := by
  simp [olsHuberWhiteHC2VarianceEstimator]

/-- In the linear model, HC3 uses annihilator-transformed errors. -/
theorem olsHuberWhiteHC3VarianceEstimator_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsHuberWhiteHC3VarianceEstimator X (X *ᵥ β + e) =
      olsConditionalVarianceMatrix X
        (Matrix.diagonal fun i =>
          ((1 - hatMatrix X i i)⁻¹) ^ 2 * (annihilatorMatrix X *ᵥ e) i ^ 2) := by
  simp [olsHuberWhiteHC3VarianceEstimator]

/-- Diagonal entries of the annihilator are `1 - hᵢᵢ`. -/
theorem annihilatorMatrix_diag_eq_one_sub_hat
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] (i : n) :
    annihilatorMatrix X i i = 1 - hatMatrix X i i := by
  simp [annihilatorMatrix]

/-- For a symmetric idempotent annihilator matrix, each row's squared norm is its diagonal
entry. -/
theorem annihilatorMatrix_row_sq_sum_eq_diag
    (X : Matrix n k ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] (i : n) :
    (∑ j, annihilatorMatrix X i j * annihilatorMatrix X i j) =
      annihilatorMatrix X i i := by
  let M : Matrix n n ℝ := annihilatorMatrix X
  calc
    (∑ j, annihilatorMatrix X i j * annihilatorMatrix X i j) =
        (M * Mᵀ) i i := by
          simp [M, Matrix.mul_apply, Matrix.transpose_apply]
    _ = (M * M) i i := by
          rw [show Mᵀ = M by simpa [M] using annihilatorMatrix_transpose X]
    _ = M i i := by
          rw [show M * M = M by simpa [M] using annihilatorMatrix_idempotent X]

/-- In the linear model, clustered covariance uses cluster-summed annihilator scores. -/
theorem olsClusteredVarianceEstimator_linear_model
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsClusteredVarianceEstimator X (X *ᵥ β + e) cluster =
      let s : G → k → ℝ := fun g a =>
        ∑ i, (if cluster i = g then (annihilatorMatrix X *ᵥ e) i * X i a else 0)
      ⅟ (Xᵀ * X) *
        (∑ g, Matrix.vecMulVec (s g) (s g)) *
        ⅟ (Xᵀ * X) := by
  simp [olsClusteredVarianceEstimator]

/-- In the linear model, the cluster residual block is the corresponding block
of the annihilator-transformed structural errors. -/
theorem clusterResidual_linear_model
    {G : Type*} (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    (cluster : n → G) (g : G) [DecidableEq n] [Invertible (Xᵀ * X)] :
    clusterResidual X (X *ᵥ β + e) cluster g =
      fun i => (annihilatorMatrix X *ᵥ e) i.1 := by
  ext i
  simp [clusterResidual]

/-- In the linear model, CR3 cluster residuals are the leave-cluster-out
adjustment applied to the annihilator-transformed structural errors. -/
theorem clusterCR3Residual_linear_model
    {G : Type*} [DecidableEq G]
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    [Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)] :
    clusterCR3Residual X (X *ᵥ β + e) cluster g =
      ⅟ (clusterLeaveOutAdjustmentMatrix X cluster g) *ᵥ
        (fun i : ClusterIndex cluster g => (annihilatorMatrix X *ᵥ e) i.1) := by
  unfold clusterCR3Residual
  rw [clusterResidual_linear_model]

/-- In the linear model, the CR3 cluster score is a deterministic linear
transform of the annihilator-transformed structural errors. -/
theorem clusterCR3Score_linear_model
    {G : Type*} [DecidableEq G]
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (cluster : n → G) (g : G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    [Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)] :
    clusterCR3Score X (X *ᵥ β + e) cluster g =
      (clusterDesign X cluster g)ᵀ *ᵥ
        (⅟ (clusterLeaveOutAdjustmentMatrix X cluster g) *ᵥ
          (fun i : ClusterIndex cluster g => (annihilatorMatrix X *ᵥ e) i.1)) := by
  unfold clusterCR3Score
  rw [clusterCR3Residual_linear_model]

/-- In the linear model, the CR3 score middle is the clusterwise outer product
of the adjusted annihilator-error scores. -/
theorem clusterCR3ScoreMiddle_linear_model
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g)) :
    clusterCR3ScoreMiddle X (X *ᵥ β + e) cluster hInv =
      ∑ g,
        letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
        let s : k → ℝ :=
          (clusterDesign X cluster g)ᵀ *ᵥ
            (⅟ (clusterLeaveOutAdjustmentMatrix X cluster g) *ᵥ
              (fun i : ClusterIndex cluster g => (annihilatorMatrix X *ᵥ e) i.1))
        Matrix.vecMulVec s s := by
  unfold clusterCR3ScoreMiddle
  refine Finset.sum_congr rfl ?_
  intro g _
  letI : Invertible (clusterLeaveOutAdjustmentMatrix X cluster g) := hInv g
  rw [clusterCR3Score_linear_model]

/-- Hansen's method-of-moments residual variance estimator
`σ̂² = n⁻¹∑ᵢ êᵢ²`. -/
noncomputable def olsSigmaSqHat
    (X : Matrix n k ℝ) (y : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] : ℝ :=
  (Fintype.card n : ℝ)⁻¹ *
    dotProduct (annihilatorMatrix X *ᵥ y) (annihilatorMatrix X *ᵥ y)

/-- Finite-sample residual variance estimator in the homoskedastic linear regression model. -/
noncomputable def olsResidualVarianceEstimator
    (X : Matrix n k ℝ) (y : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] : ℝ :=
  (dotProduct (annihilatorMatrix X *ᵥ y) (annihilatorMatrix X *ᵥ y)) /
    (Fintype.card n - Fintype.card k : ℝ)

/-- The OLS residual sum of squares `RSS = ê'ê`. This is the likelihood-scale quadratic form that
appears in Hansen's Chapter 5 likelihood-ratio / F-test derivation. -/
noncomputable def olsResidualSumSquares
    (X : Matrix n k ℝ) (y : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] : ℝ :=
  dotProduct (annihilatorMatrix X *ᵥ y) (annihilatorMatrix X *ᵥ y)

/-- Under the linear model, the residual variance estimator is the residual quadratic form
 divided by `n-k`, expressed directly in terms of the model error. -/
theorem olsResidualVarianceEstimator_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsResidualVarianceEstimator X (X *ᵥ β + e)
      = (dotProduct (annihilatorMatrix X *ᵥ e) (annihilatorMatrix X *ᵥ e)) /
          (Fintype.card n - Fintype.card k : ℝ) := by
  unfold olsResidualVarianceEstimator
  have hMXβ : annihilatorMatrix X *ᵥ (X *ᵥ β) = 0 := by
    simpa [Matrix.mulVec_mulVec] using
      congrArg (fun M : Matrix n k ℝ => M *ᵥ β) (annihilator_mul_X X)
  rw [Matrix.mulVec_add, hMXβ, zero_add]

/-- The residual sum of squares in the linear model is the annihilator quadratic form `e'Me`. -/
theorem residual_quadratic_form_of_linear_model
    (X : Matrix n k ℝ) (e : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    dotProduct (annihilatorMatrix X *ᵥ e) (annihilatorMatrix X *ᵥ e)
      = e ⬝ᵥ (annihilatorMatrix X) *ᵥ e := by
  symm
  exact quadratic_form_eq_dotProduct_of_symm_idempotent
    (annihilatorMatrix X)
    (annihilatorMatrix_transpose X)
    (annihilatorMatrix_idempotent X)
    e

/-- Under the linear model, the residual sum of squares can be written directly in terms of the
model error. -/
theorem olsResidualSumSquares_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsResidualSumSquares X (X *ᵥ β + e) =
      dotProduct (annihilatorMatrix X *ᵥ e) (annihilatorMatrix X *ᵥ e) := by
  unfold olsResidualSumSquares
  have hMXβ : annihilatorMatrix X *ᵥ (X *ᵥ β) = 0 := by
    simpa [Matrix.mulVec_mulVec] using
      congrArg (fun M : Matrix n k ℝ => M *ᵥ β) (annihilator_mul_X X)
  rw [Matrix.mulVec_add, hMXβ, zero_add]

/-- Under the linear model, the residual sum of squares is the annihilator quadratic form `e'Me`.
This is the likelihood-scale version of the Chapter 5 variance identity. -/
theorem olsResidualSumSquares_linear_model_quadratic_form
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsResidualSumSquares X (X *ᵥ β + e) = e ⬝ᵥ (annihilatorMatrix X) *ᵥ e := by
  rw [olsResidualSumSquares_linear_model]
  exact residual_quadratic_form_of_linear_model X e

/-- Under the linear model, Hansen's `σ̂² = n⁻¹∑ᵢ êᵢ²` is the annihilator
quadratic form scaled by `1 / n`. -/
theorem olsSigmaSqHat_linear_model_quadratic_form
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsSigmaSqHat X (X *ᵥ β + e) =
      (Fintype.card n : ℝ)⁻¹ * (e ⬝ᵥ (annihilatorMatrix X) *ᵥ e) := by
  unfold olsSigmaSqHat
  have hMXβ : annihilatorMatrix X *ᵥ (X *ᵥ β) = 0 := by
    simpa [Matrix.mulVec_mulVec] using
      congrArg (fun M : Matrix n k ℝ => M *ᵥ β) (annihilator_mul_X X)
  rw [Matrix.mulVec_add, hMXβ, zero_add, residual_quadratic_form_of_linear_model]

/-- Under the linear model, the residual variance estimator is the annihilator quadratic form
divided by `n-k`. This is the deterministic identity underlying the chi-square step. -/
theorem olsResidualVarianceEstimator_linear_model_quadratic_form
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsResidualVarianceEstimator X (X *ᵥ β + e)
      = (e ⬝ᵥ (annihilatorMatrix X) *ᵥ e) /
          (Fintype.card n - Fintype.card k : ℝ) := by
  rw [olsResidualVarianceEstimator_linear_model, residual_quadratic_form_of_linear_model]



/-- Deterministic core of the Gauss-Markov theorem: the variance-gap matrix is positive
semidefinite. -/
theorem gaussMarkov_variance_gap_posSemidef
    (X A : Matrix n k ℝ) [Invertible (Xᵀ * X)]
    (hAX : Aᵀ * X = (1 : Matrix k k ℝ)) :
    (Aᵀ * A - ⅟ (Xᵀ * X)).PosSemidef := by
  let C : Matrix k n ℝ := Aᵀ - ⅟ (Xᵀ * X) * Xᵀ
  have hgap : C * Cᵀ = Aᵀ * A - ⅟ (Xᵀ * X) := by
    have hXA : Xᵀ * A = (1 : Matrix k k ℝ) := by
      simpa using congrArg Matrix.transpose hAX
    dsimp [C]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, inv_gram_transpose]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have h1 : Aᵀ * (X * ⅟ (Xᵀ * X)) = ⅟ (Xᵀ * X) := by
      calc
        Aᵀ * (X * ⅟ (Xᵀ * X)) = (Aᵀ * X) * ⅟ (Xᵀ * X) := by rw [Matrix.mul_assoc]
        _ = 1 * ⅟ (Xᵀ * X) := by rw [hAX]
        _ = ⅟ (Xᵀ * X) := by simp
    have h2' : (Xᵀ * X)⁻¹ - (Xᵀ * X)⁻¹ * (Xᵀ * (X * (Xᵀ * X)⁻¹)) = 0 := by
      have hcancel : Xᵀ * (X * (Xᵀ * X)⁻¹) = (1 : Matrix k k ℝ) := by
        rw [← Matrix.mul_assoc]
        simpa only [invOf_eq_nonsing_inv] using (mul_invOf_self (Xᵀ * X))
      rw [hcancel]
      simp
    have h1' : Aᵀ * (X * (Xᵀ * X)⁻¹) = (Xᵀ * X)⁻¹ := by
      simpa using h1
    simp only [transpose_transpose, invOf_eq_nonsing_inv]
    rw [h1']
    rw [Matrix.mul_assoc ((Xᵀ * X)⁻¹) Xᵀ A, hXA, Matrix.mul_one]
    rw [Matrix.mul_assoc ((Xᵀ * X)⁻¹) Xᵀ (X * (Xᵀ * X)⁻¹)]
    rw [h2']
    abel_nf
  have hpsd : (C * Cᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose, Matrix.transpose_transpose] using
      (Matrix.posSemidef_self_mul_conjTranspose C)
  simpa [hgap] using hpsd

section ConditionalUnbiasedness

open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open MeasureTheory

variable {Ω : Type*}
variable {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}

omit [DecidableEq k] in
/-- Conditional expectation commutes with a deterministic matrix sandwich.

If every entry of the random middle matrix has conditional expectation equal to
the corresponding entry of `M₀`, then the deterministic sandwich `A M A` has
conditional expectation `A M₀ A`. -/
theorem condExp_deterministic_sandwich_eq
    (A : Matrix k k ℝ) (M : Ω → Matrix k k ℝ) (M₀ : Matrix k k ℝ)
    [IsProbabilityMeasure μ]
    (hM_int : ∀ c d : k, Integrable (fun ω => M ω c d) μ)
    (hM_cond : ∀ c d : k,
      μ[(fun ω => M ω c d) | m] =ᵐ[μ] fun _ => M₀ c d) :
    μ[(fun ω => fun a b => (A * M ω * A) a b) | m] =ᵐ[μ]
      fun _ a b => (A * M₀ * A) a b := by
  let f : Ω → k → k → ℝ := fun ω a b => (A * M ω * A) a b
  have hentry : ∀ (ω : Ω) (a b : k),
      f ω a b = ∑ c, ∑ d, (A a c * A d b) * M ω c d := by
    intro ω a b
    calc
      f ω a b =
          ∑ d, (∑ c, A a c * M ω c d) * A d b := by
            simp [f, Matrix.mul_apply]
      _ = ∑ d, ∑ c, (A a c * M ω c d) * A d b := by
            refine Finset.sum_congr rfl ?_
            intro d _
            rw [Finset.sum_mul]
      _ = ∑ c, ∑ d, (A a c * M ω c d) * A d b := by
            rw [Finset.sum_comm]
      _ = ∑ c, ∑ d, (A a c * A d b) * M ω c d := by
            refine Finset.sum_congr rfl ?_
            intro c _
            refine Finset.sum_congr rfl ?_
            intro d _
            ring
  have htarget_entry : ∀ a b : k,
      (A * M₀ * A) a b = ∑ c, ∑ d, (A a c * A d b) * M₀ c d := by
    intro a b
    calc
      (A * M₀ * A) a b =
          ∑ d, (∑ c, A a c * M₀ c d) * A d b := by
            simp [Matrix.mul_apply]
      _ = ∑ d, ∑ c, (A a c * M₀ c d) * A d b := by
            refine Finset.sum_congr rfl ?_
            intro d _
            rw [Finset.sum_mul]
      _ = ∑ c, ∑ d, (A a c * M₀ c d) * A d b := by
            rw [Finset.sum_comm]
      _ = ∑ c, ∑ d, (A a c * A d b) * M₀ c d := by
            refine Finset.sum_congr rfl ?_
            intro c _
            refine Finset.sum_congr rfl ?_
            intro d _
            ring
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro a
    refine Integrable.of_eval ?_
    intro b
    have hrepr :
        (fun ω => f ω a b) =
          fun ω => ∑ c, ∑ d, (A a c * A d b) * M ω c d := by
      funext ω
      exact hentry ω a b
    rw [hrepr]
    exact MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun c ω => ∑ d, (A a c * A d b) * M ω c d)
      (fun c _ =>
        MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun d ω => (A a c * A d b) * M ω c d)
          (fun d _ => (hM_int c d).const_mul (A a c * A d b)))
  rw [Filter.EventuallyEq]
  change ∀ᵐ ω ∂μ, μ[f | m] ω = fun a b => (A * M₀ * A) a b
  have hcoord : ∀ a b : k, ∀ᵐ ω ∂μ,
      μ[f | m] ω a b = (A * M₀ * A) a b := by
    intro a b
    have hrepr :
        (fun ω => f ω a b) =
          fun ω => ∑ c, ∑ d, (A a c * A d b) * M ω c d := by
      funext ω
      exact hentry ω a b
    have hsum :
        μ[(fun ω => f ω a b) | m] =ᵐ[μ]
          fun _ => (A * M₀ * A) a b := by
      rw [hrepr]
      have houter :
          μ[(fun ω => ∑ c, ∑ d, (A a c * A d b) * M ω c d) | m] =ᵐ[μ]
            ∑ c, μ[(fun ω => ∑ d, (A a c * A d b) * M ω c d) | m] := by
        have hsum_repr :
            (fun ω => ∑ c, ∑ d, (A a c * A d b) * M ω c d) =
              ∑ c, fun ω => ∑ d, (A a c * A d b) * M ω c d := by
          funext ω
          simp
        rw [hsum_repr]
        simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
          (s := Finset.univ)
          (f := fun c ω => ∑ d, (A a c * A d b) * M ω c d)
          (fun c _ =>
            MeasureTheory.integrable_finset_sum (s := Finset.univ)
              (f := fun d ω => (A a c * A d b) * M ω c d)
              (fun d _ => (hM_int c d).const_mul (A a c * A d b)))
      have hinner : ∀ c,
          μ[(fun ω => ∑ d, (A a c * A d b) * M ω c d) | m] =ᵐ[μ]
            fun _ => ∑ d, (A a c * A d b) * M₀ c d := by
        intro c
        have hinner_sum :
            μ[(fun ω => ∑ d, (A a c * A d b) * M ω c d) | m] =ᵐ[μ]
              ∑ d, μ[(fun ω => (A a c * A d b) * M ω c d) | m] := by
          have hsum_repr :
              (fun ω => ∑ d, (A a c * A d b) * M ω c d) =
                ∑ d, fun ω => (A a c * A d b) * M ω c d := by
            funext ω
            simp
          rw [hsum_repr]
          simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
            (s := Finset.univ)
            (f := fun d ω => (A a c * A d b) * M ω c d)
            (fun d _ => (hM_int c d).const_mul (A a c * A d b))
        have hcoord_smul : ∀ d,
            μ[(fun ω => (A a c * A d b) * M ω c d) | m] =ᵐ[μ]
              fun _ => (A a c * A d b) * M₀ c d := by
          intro d
          refine (MeasureTheory.condExp_smul (μ := μ) (m := m)
            (A a c * A d b) (fun ω => M ω c d)).trans ?_
          filter_upwards [hM_cond c d] with ω hω
          simp [Pi.smul_apply, smul_eq_mul, hω]
        refine hinner_sum.trans ?_
        have hall : ∀ᵐ ω ∂μ, ∀ d,
            μ[(fun ω => (A a c * A d b) * M ω c d) | m] ω =
              (A a c * A d b) * M₀ c d := by
          exact ae_all_iff.2 fun d => hcoord_smul d
        filter_upwards [hall] with ω hω
        calc
          ((∑ d, μ[(fun ω => (A a c * A d b) * M ω c d) | m]) : Ω → ℝ) ω =
              ∑ d, μ[(fun ω => (A a c * A d b) * M ω c d) | m] ω := by
                simp
          _ = ∑ d, (A a c * A d b) * M₀ c d := by
                exact Finset.sum_congr rfl fun d _ => hω d
      refine houter.trans ?_
      have hall : ∀ᵐ ω ∂μ, ∀ c,
          μ[(fun ω => ∑ d, (A a c * A d b) * M ω c d) | m] ω =
            ∑ d, (A a c * A d b) * M₀ c d := by
        exact ae_all_iff.2 fun c => hinner c
      filter_upwards [hall] with ω hω
      calc
        ((∑ c, μ[(fun ω => ∑ d, (A a c * A d b) * M ω c d) | m]) :
            Ω → ℝ) ω =
            ∑ c, μ[(fun ω => ∑ d, (A a c * A d b) * M ω c d) | m] ω := by
              simp
        _ = ∑ c, ∑ d, (A a c * A d b) * M₀ c d := by
              exact Finset.sum_congr rfl fun c _ => hω c
        _ = (A * M₀ * A) a b := by
              exact (htarget_entry a b).symm
    exact (condExp_apply_apply (m := m) (μ := μ) (f := f) hf_int a b).trans hsum
  have hall : ∀ᵐ ω ∂μ, ∀ a b : k,
      μ[f | m] ω a b = (A * M₀ * A) a b := by
    exact ae_all_iff.2 fun a => ae_all_iff.2 fun b => hcoord a b
  exact hall.mono fun ω hω => by
    funext a b
    exact hω a b

/-- Conditional expectation of the CR3 clustered sandwich from a conditional
expectation for its CR3 score-middle matrix. -/
theorem condExp_olsClusteredCR3VarianceEstimator_eq_sandwich_of_middle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : Ω → n → ℝ) (cluster : n → G)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g))
    [IsProbabilityMeasure μ]
    (Mcr3 : Matrix k k ℝ)
    (hmiddle_int : ∀ a b : k,
      Integrable (fun ω => clusterCR3ScoreMiddle X (y ω) cluster hInv a b) μ)
    (hmiddle_cond : ∀ a b : k,
      μ[(fun ω => clusterCR3ScoreMiddle X (y ω) cluster hInv a b) | m] =ᵐ[μ]
        fun _ => Mcr3 a b) :
    μ[(fun ω => fun a b =>
      olsClusteredCR3VarianceEstimator X (y ω) cluster hInv a b) | m] =ᵐ[μ]
      fun _ a b => (⅟ (Xᵀ * X) * Mcr3 * ⅟ (Xᵀ * X)) a b := by
  let A : Matrix k k ℝ := ⅟ (Xᵀ * X)
  let middle : Ω → Matrix k k ℝ := fun ω => clusterCR3ScoreMiddle X (y ω) cluster hInv
  have hsandwich := condExp_deterministic_sandwich_eq
    (μ := μ) (m := m) A middle Mcr3 hmiddle_int hmiddle_cond
  have hleft :
      (fun ω => fun a b =>
        olsClusteredCR3VarianceEstimator X (y ω) cluster hInv a b) =
        fun ω => fun a b => (A * middle ω * A) a b := by
    funext ω a b
    have h :=
      olsClusteredCR3VarianceEstimator_eq_clusterCR3ScoreMiddle X (y ω) cluster hInv
    simpa [A, middle] using congrFun (congrFun h a) b
  rw [hleft]
  simpa [A, middle]
    using hsandwich

/-- Conditional CR3 conservativeness bridge for the clustered covariance target.

Once the conditional expected CR3 score middle dominates Hansen's clustered
covariance middle, the conditional expected CR3 sandwich dominates the
clustered OLS covariance matrix from equation (4.47). -/
theorem condExp_olsClusteredCR3VarianceEstimator_conservative_of_middle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : Ω → n → ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g))
    [IsProbabilityMeasure μ]
    (Mcr3 : Matrix k k ℝ)
    (hmiddle_int : ∀ a b : k,
      Integrable (fun ω => clusterCR3ScoreMiddle X (y ω) cluster hInv a b) μ)
    (hmiddle_cond : ∀ a b : k,
      μ[(fun ω => clusterCR3ScoreMiddle X (y ω) cluster hInv a b) | m] =ᵐ[μ]
        fun _ => Mcr3 a b)
    (hmiddle :
      (Mcr3 - clusterCovarianceMiddle X cluster Sigma).PosSemidef) :
    ∀ᵐ ω ∂μ,
      (Matrix.of (fun a b =>
        μ[(fun ω => fun a b =>
          olsClusteredCR3VarianceEstimator X (y ω) cluster hInv a b) | m] ω a b) -
        olsClusterConditionalVarianceMatrix X cluster Sigma).PosSemidef := by
  have hcond := condExp_olsClusteredCR3VarianceEstimator_eq_sandwich_of_middle
    (μ := μ) (m := m) X y cluster hInv Mcr3 hmiddle_int hmiddle_cond
  filter_upwards [hcond] with ω hω
  have hmatrix :
      Matrix.of (fun a b =>
        μ[(fun ω => fun a b =>
          olsClusteredCR3VarianceEstimator X (y ω) cluster hInv a b) | m] ω a b) =
        ⅟ (Xᵀ * X) * Mcr3 * ⅟ (Xᵀ * X) := by
    ext a b
    exact congrFun (congrFun hω a) b
  rw [hmatrix]
  change ((⅟ (Xᵀ * X) * Mcr3 * ⅟ (Xᵀ * X)) -
    olsClusterConditionalVarianceMatrix X cluster Sigma).PosSemidef
  simpa [olsClusterConditionalVarianceMatrix] using
    olsSandwichMiddle_mono_posSemidef
      (X := X)
      (M₁ := clusterCovarianceMiddle X cluster Sigma)
      (M₂ := Mcr3)
      hmiddle

/-- Conditional CR3 conservativeness from blockwise covariance dominance.

If the conditional expected CR3 score middle is represented by cluster blocks
`Γ_g`, and each `Γ_g` dominates Hansen's target block `Σ_g`, then the
conditional expected CR3 sandwich dominates the clustered OLS covariance matrix. -/
theorem condExp_olsClusteredCR3VarianceEstimator_conservative_of_block_middle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (y : Ω → n → ℝ) (cluster : n → G)
    (Sigma Gamma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)]
    (hInv : ∀ g, Invertible (clusterLeaveOutAdjustmentMatrix X cluster g))
    [IsProbabilityMeasure μ]
    (hmiddle_int : ∀ a b : k,
      Integrable (fun ω => clusterCR3ScoreMiddle X (y ω) cluster hInv a b) μ)
    (hmiddle_cond : ∀ a b : k,
      μ[(fun ω => clusterCR3ScoreMiddle X (y ω) cluster hInv a b) | m] =ᵐ[μ]
        fun _ => clusterCovarianceMiddle X cluster Gamma a b)
    (hGamma : ∀ g, (Gamma g - Sigma g).PosSemidef) :
    ∀ᵐ ω ∂μ,
      (Matrix.of (fun a b =>
        μ[(fun ω => fun a b =>
          olsClusteredCR3VarianceEstimator X (y ω) cluster hInv a b) | m] ω a b) -
        olsClusterConditionalVarianceMatrix X cluster Sigma).PosSemidef :=
  condExp_olsClusteredCR3VarianceEstimator_conservative_of_middle
    (μ := μ) (m := m) X y cluster Sigma hInv
    (clusterCovarianceMiddle X cluster Gamma)
    hmiddle_int hmiddle_cond
    (clusterCovarianceMiddle_mono_posSemidef X cluster Sigma Gamma hGamma)

/-- Private proof engine. Conditional expectation of the random quadratic form `e' M e`
reduces to the deterministic double sum `∑ᵢⱼ Mᵢⱼ Dᵢⱼ` whenever the entrywise second-moment
matrix `E[eᵢeⱼ | m] = Dᵢⱼ` is a.e. constant on the conditioning σ-algebra.

This is the linearity-of-conditional-expectation core used by
`ols_condExp_residualVarianceEstimator_eq_sigmaSq`. The proof pulls the deterministic matrix
entries `Mᵢⱼ` out of the conditional expectation and then evaluates each `E[eᵢeⱼ | m]` against
`Dᵢⱼ` under the hypothesis `hD`. -/
private theorem condExp_quadratic_form_eq_sum
    (M : Matrix n n ℝ) (e : Ω → n → ℝ) (D : Matrix n n ℝ)
    [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i j, Integrable (fun ω => e ω i * e ω j) μ)
    (hD : ∀ i j, μ[fun ω => e ω i * e ω j | m] =ᵐ[μ] fun _ => D i j) :
    μ[fun ω => e ω ⬝ᵥ M *ᵥ e ω | m] =ᵐ[μ]
      fun _ => ∑ i, ∑ j, M i j * D i j := by
  have hrepr : (fun ω => e ω ⬝ᵥ M *ᵥ e ω) =
      fun ω => ∑ i, ∑ j, M i j * (e ω i * e ω j) := by
    funext ω
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm]
  rw [hrepr]
  have hsum1 :
      μ[(fun ω => ∑ i, ∑ j, M i j * (e ω i * e ω j)) | m] =ᵐ[μ]
        ∑ i, μ[(fun ω => ∑ j, M i j * (e ω i * e ω j)) | m] := by
    have hsum_repr :
        (fun ω => ∑ i, ∑ j, M i j * (e ω i * e ω j)) =
          ∑ i, fun ω => ∑ j, M i j * (e ω i * e ω j) := by
      funext ω
      simp
    rw [hsum_repr]
    simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
      (s := Finset.univ)
      (f := fun i ω => ∑ j, M i j * (e ω i * e ω j))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun j ω => M i j * (e ω i * e ω j))
          (fun j _ => (hee_int i j).const_mul (M i j)))
  have hsum2 :
      (∑ i, μ[(fun ω => ∑ j, M i j * (e ω i * e ω j)) | m]) =ᵐ[μ]
        ∑ i, ∑ j, (fun _ : Ω => M i j * D i j) := by
    have hinner : ∀ i,
        μ[(fun ω => ∑ j, M i j * (e ω i * e ω j)) | m] =ᵐ[μ]
          ∑ j, μ[(fun ω => M i j * (e ω i * e ω j)) | m] := by
      intro i
      have hinner_repr :
          (fun ω => ∑ j, M i j * (e ω i * e ω j)) =
            ∑ j, fun ω => M i j * (e ω i * e ω j) := by
        funext ω
        simp
      rw [hinner_repr]
      simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
        (s := Finset.univ)
        (f := fun j ω => M i j * (e ω i * e ω j))
        (fun j _ => (hee_int i j).const_mul (M i j))
    have hcoord : ∀ i j,
        μ[(fun ω => M i j * (e ω i * e ω j)) | m] =ᵐ[μ]
          fun _ => M i j * D i j := by
      intro i j
      refine (MeasureTheory.condExp_smul (μ := μ) (m := m) (M i j)
        (fun ω => e ω i * e ω j)).trans ?_
      filter_upwards [hD i j] with ω hω
      simp [Pi.smul_apply, smul_eq_mul, hω]
    have hall1 : ∀ᵐ ω ∂μ, ∀ i,
        μ[(fun ω => ∑ j, M i j * (e ω i * e ω j)) | m] ω =
          ∑ j, μ[(fun ω => M i j * (e ω i * e ω j)) | m] ω := by
      exact ae_all_iff.2 fun i => by simpa [Filter.EventuallyEq] using hinner i
    have hall2 : ∀ᵐ ω ∂μ, ∀ i, ∀ j,
        μ[(fun ω => M i j * (e ω i * e ω j)) | m] ω = M i j * D i j := by
      exact ae_all_iff.2 fun i => ae_all_iff.2 fun j => hcoord i j
    filter_upwards [hall1, hall2] with ω h1 h2
    simp [h1, h2]
  exact (hsum1.trans hsum2).trans <| by
    filter_upwards [] with ω
    simp

/-- Private proof engine. Homoskedastic specialization of the previous double sum: when the
conditional second-moment matrix is `σ² · I`, the sum `∑ᵢⱼ Mᵢⱼ (σ² · δᵢⱼ)` collapses to
`σ² · tr(M)`. Used together with `condExp_quadratic_form_eq_sum` to discharge the
`E[s² | X] = σ²` step against `tr(M) = n - k`. -/
private theorem sum_quadratic_homoskedastic_eq_trace
    (M : Matrix n n ℝ) [DecidableEq n] (σ2 : ℝ) :
    (∑ i, ∑ j, M i j * (σ2 * (1 : Matrix n n ℝ) i j)) = σ2 * Matrix.trace M := by
  classical
  rw [Matrix.trace]
  calc
    (∑ i, ∑ j, M i j * (σ2 * (1 : Matrix n n ℝ) i j)) = ∑ i, M i i * σ2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_eq_single i]
      · simp [mul_comm]
      · intro j _ hji
        simp [hji.symm]
      · intro hi
        simp at hi
    _ = σ2 * ∑ i, M i i := by
      rw [Finset.mul_sum]
      simp [mul_comm]

/-- Under homoskedastic conditional second moments, the conditional expectation of a squared
annihilator-row residual is `σ²(1-hᵢᵢ)`. -/
theorem condExp_annihilator_row_sq_eq_homoskedastic
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (σ2 : ℝ) (i : n)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_homo : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => σ2 * (1 : Matrix n n ℝ) r s) :
    μ[fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m] =ᵐ[μ]
      fun _ => σ2 * (1 - hatMatrix X i i) := by
  let M : Matrix n n ℝ := annihilatorMatrix X
  let A : Matrix n n ℝ := Matrix.vecMulVec (M i) (M i)
  have hrepr : (fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2) =
      fun ω => e ω ⬝ᵥ A *ᵥ e ω := by
    funext ω
    simp [A, M, Matrix.mulVec, Matrix.vecMulVec, dotProduct, pow_two,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hrepr]
  have hquad := condExp_quadratic_form_eq_sum (μ := μ) (m := m) (m₀ := m₀)
    A e (σ2 • (1 : Matrix n n ℝ)) hm hee_int
    (fun r s => by simpa [Pi.smul_apply, smul_eq_mul] using hee_homo r s)
  refine hquad.trans ?_
  filter_upwards [] with ω
  calc
    (∑ r, ∑ s, A r s * (σ2 • (1 : Matrix n n ℝ)) r s)
        = σ2 * ∑ r, M i r * M i r := by
          have hdiag :
              (∑ r, ∑ s, A r s * (σ2 • (1 : Matrix n n ℝ)) r s) =
                ∑ r, σ2 * (M i r * M i r) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [Finset.sum_eq_single r]
            · simp [A, Matrix.vecMulVec, smul_eq_mul, mul_comm]
            · intro s _ hsr
              have hone : (1 : Matrix n n ℝ) r s = 0 := by
                simp [hsr.symm]
              simp [A, Matrix.vecMulVec, smul_eq_mul, hone]
            · intro hr
              simp at hr
          rw [hdiag, Finset.mul_sum]
    _ = σ2 * (1 - hatMatrix X i i) := by
          rw [annihilatorMatrix_row_sq_sum_eq_diag X i]
          simp [annihilatorMatrix_diag_eq_one_sub_hat]

/-- Under diagonal heteroskedastic conditional second moments, the conditional expectation of a
squared annihilator-row residual is the row-weighted diagonal variance sum. -/
theorem condExp_annihilator_row_sq_eq_diagonal
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (σ2 : n → ℝ) (i : n)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_diag : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => (Matrix.diagonal σ2) r s) :
    μ[fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m] =ᵐ[μ]
      fun _ => ∑ r, annihilatorMatrix X i r * annihilatorMatrix X i r * σ2 r := by
  let M : Matrix n n ℝ := annihilatorMatrix X
  let A : Matrix n n ℝ := Matrix.vecMulVec (M i) (M i)
  have hrepr : (fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2) =
      fun ω => e ω ⬝ᵥ A *ᵥ e ω := by
    funext ω
    simp [A, M, Matrix.mulVec, Matrix.vecMulVec, dotProduct, pow_two,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hrepr]
  have hquad := condExp_quadratic_form_eq_sum (μ := μ) (m := m) (m₀ := m₀)
    A e (Matrix.diagonal σ2) hm hee_int hee_diag
  refine hquad.trans ?_
  filter_upwards [] with ω
  have hdiag :
      (∑ r, ∑ s, A r s * (Matrix.diagonal σ2) r s) =
        ∑ r, M i r * M i r * σ2 r := by
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.sum_eq_single r]
    · simp [A, Matrix.vecMulVec, Matrix.diagonal, mul_comm]
    · intro s _ hsr
      simp [A, Matrix.vecMulVec, Matrix.diagonal, hsr.symm]
    · intro hr
      simp at hr
  simpa [M] using hdiag

/-- HC2's leverage adjustment is conditionally unbiased for the homoskedastic variance at each
row when `hᵢᵢ ≠ 1`. -/
theorem condExp_HC2_adjusted_annihilator_row_sq_eq_sigmaSq
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (σ2 : ℝ) (i : n)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_homo : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => σ2 * (1 : Matrix n n ℝ) r s)
    (hlev_ne : 1 - hatMatrix X i i ≠ 0) :
    μ[fun ω =>
        (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m]
      =ᵐ[μ] fun _ => σ2 := by
  have hscale :
      μ[fun ω =>
          (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m]
        =ᵐ[μ]
          fun ω => (1 - hatMatrix X i i)⁻¹ *
            μ[fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul (μ := μ) (m := m) (1 - hatMatrix X i i)⁻¹
        (fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2))
  have hrow :=
    condExp_annihilator_row_sq_eq_homoskedastic
      (μ := μ) (m := m) X e σ2 i hm hee_int hee_homo
  refine hscale.trans ?_
  filter_upwards [hrow] with ω hω
  rw [hω]
  field_simp [hlev_ne]

/-- Exact HC2 row expectation under diagonal heteroskedastic conditional second moments. -/
theorem condExp_HC2_adjusted_annihilator_row_sq_eq_diagonal
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (σ2 : n → ℝ) (i : n)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_diag : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => (Matrix.diagonal σ2) r s) :
    μ[fun ω =>
        (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m]
      =ᵐ[μ] fun _ =>
        (1 - hatMatrix X i i)⁻¹ *
          ∑ r, annihilatorMatrix X i r * annihilatorMatrix X i r * σ2 r := by
  have hscale :
      μ[fun ω =>
          (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m]
        =ᵐ[μ]
          fun ω => (1 - hatMatrix X i i)⁻¹ *
            μ[fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul (μ := μ) (m := m) (1 - hatMatrix X i i)⁻¹
        (fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2))
  have hrow :=
    condExp_annihilator_row_sq_eq_diagonal
      (μ := μ) (m := m) X e σ2 i hm hee_int hee_diag
  refine hscale.trans ?_
  filter_upwards [hrow] with ω hω
  simp [hω]

/-- HC3's leverage adjustment has one extra inverse-leverage factor in the homoskedastic row
expectation. -/
theorem condExp_HC3_adjusted_annihilator_row_sq_eq_sigmaSq_mul_inv
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (σ2 : ℝ) (i : n)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_homo : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => σ2 * (1 : Matrix n n ℝ) r s)
    (hlev_ne : 1 - hatMatrix X i i ≠ 0) :
    μ[fun ω =>
        ((1 - hatMatrix X i i)⁻¹) ^ 2 * (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m]
      =ᵐ[μ] fun _ => σ2 * (1 - hatMatrix X i i)⁻¹ := by
  let c : ℝ := ((1 - hatMatrix X i i)⁻¹) ^ 2
  have hscale :
      μ[fun ω =>
          ((1 - hatMatrix X i i)⁻¹) ^ 2 * (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m]
        =ᵐ[μ]
          fun ω => ((1 - hatMatrix X i i)⁻¹) ^ 2 *
            μ[fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m] ω := by
    simpa [c, Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul (μ := μ) (m := m) c
        (fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2))
  have hrow :=
    condExp_annihilator_row_sq_eq_homoskedastic
      (μ := μ) (m := m) X e σ2 i hm hee_int hee_homo
  refine hscale.trans ?_
  filter_upwards [hrow] with ω hω
  rw [hω]
  field_simp [hlev_ne]

/-- Exact HC3 row expectation under diagonal heteroskedastic conditional second moments. -/
theorem condExp_HC3_adjusted_annihilator_row_sq_eq_diagonal
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (σ2 : n → ℝ) (i : n)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_diag : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => (Matrix.diagonal σ2) r s) :
    μ[fun ω =>
        ((1 - hatMatrix X i i)⁻¹) ^ 2 * (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m]
      =ᵐ[μ] fun _ =>
        ((1 - hatMatrix X i i)⁻¹) ^ 2 *
          ∑ r, annihilatorMatrix X i r * annihilatorMatrix X i r * σ2 r := by
  let c : ℝ := ((1 - hatMatrix X i i)⁻¹) ^ 2
  have hscale :
      μ[fun ω =>
          ((1 - hatMatrix X i i)⁻¹) ^ 2 * (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m]
        =ᵐ[μ]
          fun ω => ((1 - hatMatrix X i i)⁻¹) ^ 2 *
            μ[fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2 | m] ω := by
    simpa [c, Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul (μ := μ) (m := m) c
        (fun ω => (annihilatorMatrix X *ᵥ e ω) i ^ 2))
  have hrow :=
    condExp_annihilator_row_sq_eq_diagonal
      (μ := μ) (m := m) X e σ2 i hm hee_int hee_diag
  refine hscale.trans ?_
  filter_upwards [hrow] with ω hω
  simp [hω]

/-- Conditional expectation commutes with a deterministic diagonal covariance sandwich.

If each random diagonal entry has conditional expectation `dᵢ`, then the whole matrix-valued
sandwich has conditional expectation given by the deterministic diagonal matrix `diag(d)`. -/
theorem condExp_olsConditionalVarianceMatrix_diagonal_eq
    (X : Matrix n k ℝ) (z : Ω → n → ℝ) (d : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hz_int : ∀ i, Integrable (fun ω => z ω i) μ)
    (hz : ∀ i, μ[fun ω => z ω i | m] =ᵐ[μ] fun _ => d i) :
    μ[(fun ω => fun a b => olsConditionalVarianceMatrix X (Matrix.diagonal (z ω)) a b) | m]
      =ᵐ[μ] fun _ a b => olsConditionalVarianceMatrix X (Matrix.diagonal d) a b := by
  let f : Ω → k → k → ℝ := fun ω a b =>
    olsConditionalVarianceMatrix X (Matrix.diagonal (z ω)) a b
  let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
  have hentry : ∀ (ω : Ω) (a b : k),
      f ω a b = ∑ i, (w a i * w b i) * z ω i := by
    intro ω a b
    simp [f, w, olsConditionalVarianceMatrix_diagonal_apply]
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro a
    refine Integrable.of_eval ?_
    intro b
    have hrepr : (fun ω => f ω a b) = fun ω => ∑ i, (w a i * w b i) * z ω i := by
      funext ω
      exact hentry ω a b
    rw [hrepr]
    exact MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => (w a i * w b i) * z ω i)
      (fun i _ => (hz_int i).const_mul (w a i * w b i))
  rw [Filter.EventuallyEq]
  change ∀ᵐ ω ∂μ, μ[f | m] ω = fun a b => olsConditionalVarianceMatrix X (Matrix.diagonal d) a b
  have hcoord : ∀ a b : k, ∀ᵐ ω ∂μ,
      μ[f | m] ω a b = olsConditionalVarianceMatrix X (Matrix.diagonal d) a b := by
    intro a b
    have hrepr : (fun ω => f ω a b) = fun ω => ∑ i, (w a i * w b i) * z ω i := by
      funext ω
      exact hentry ω a b
    have hsum :
        μ[(fun ω => f ω a b) | m] =ᵐ[μ]
          fun _ => olsConditionalVarianceMatrix X (Matrix.diagonal d) a b := by
      rw [hrepr]
      have hsum_ce :
          μ[(fun ω => ∑ i, (w a i * w b i) * z ω i) | m] =ᵐ[μ]
            ∑ i, μ[(fun ω => (w a i * w b i) * z ω i) | m] := by
        have hsum_repr :
            (fun ω => ∑ i, (w a i * w b i) * z ω i) =
              ∑ i, fun ω => (w a i * w b i) * z ω i := by
          funext ω
          simp
        rw [hsum_repr]
        simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
          (s := Finset.univ)
          (f := fun i ω => (w a i * w b i) * z ω i)
          (fun i _ => (hz_int i).const_mul (w a i * w b i))
      have hcoord_smul : ∀ i,
          μ[(fun ω => (w a i * w b i) * z ω i) | m] =ᵐ[μ]
            fun _ => (w a i * w b i) * d i := by
        intro i
        refine (MeasureTheory.condExp_smul (μ := μ) (m := m) (w a i * w b i)
          (fun ω => z ω i)).trans ?_
        filter_upwards [hz i] with ω hω
        simp [Pi.smul_apply, smul_eq_mul, hω]
      have hall : ∀ᵐ ω ∂μ, ∀ i,
          μ[(fun ω => (w a i * w b i) * z ω i) | m] ω =
            (w a i * w b i) * d i := by
        exact ae_all_iff.2 fun i => hcoord_smul i
      exact hsum_ce.trans <| by
        filter_upwards [hall] with ω hω
        calc
          ((∑ i, μ[(fun ω => (w a i * w b i) * z ω i) | m]) : Ω → ℝ) ω =
              ∑ i, μ[(fun ω => (w a i * w b i) * z ω i) | m] ω := by
                simp
          _ =
              ∑ i, (w a i * w b i) * d i := by
                exact Finset.sum_congr rfl fun i _ => hω i
          _ = olsConditionalVarianceMatrix X (Matrix.diagonal d) a b := by
                symm
                simp [w, olsConditionalVarianceMatrix_diagonal_apply]
    exact (condExp_apply_apply (m := m) (μ := μ) (f := f) hf_int a b).trans hsum
  have hall : ∀ᵐ ω ∂μ, ∀ a b : k,
      μ[f | m] ω a b = olsConditionalVarianceMatrix X (Matrix.diagonal d) a b := by
    exact ae_all_iff.2 fun a => ae_all_iff.2 fun b => hcoord a b
  exact hall.mono fun ω hω => by
    funext a b
    exact hω a b

set_option maxHeartbeats 800000 in
-- The dependent cluster-index sums make the integrability and conditional-expectation
-- rewrites expensive, so keep the higher heartbeat limit local to this theorem.
omit [Fintype k] [DecidableEq k] in
/-- Coordinate form of the conditional expectation of the infeasible clustered
score middle.

If each cluster block has conditional second-moment matrix `Σ_g`, then each
entry of the infeasible score middle `∑_g (X_g'e_g)(X_g'e_g)'` has conditional
expectation equal to the matching entry of Hansen's clustered covariance middle
`∑_g X_g'Σ_gX_g` from equation (4.46). -/
theorem condExp_clusterErrorScoreMiddle_entry_eq_clusterCovarianceMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ g (i j : ClusterIndex cluster g),
      Integrable (fun ω => e ω i.1 * e ω j.1) μ)
    (hSigma : ∀ g (i j : ClusterIndex cluster g),
      μ[fun ω => e ω i.1 * e ω j.1 | m] =ᵐ[μ] fun _ => Sigma g i j)
    (a b : k)
    (hscore_int : ∀ g,
      Integrable
        (fun ω =>
          clusterErrorScore X (e ω) cluster g a *
            clusterErrorScore X (e ω) cluster g b) μ) :
    μ[(fun ω =>
      (∑ g, Matrix.vecMulVec (clusterErrorScore X (e ω) cluster g)
        (clusterErrorScore X (e ω) cluster g)) a b) | m] =ᵐ[μ]
      fun _ => clusterCovarianceMiddle X cluster Sigma a b := by
  let s : G → Ω → ℝ := fun g ω =>
    clusterErrorScore X (e ω) cluster g a *
      clusterErrorScore X (e ω) cluster g b
  have hleft :
      (fun ω =>
        (∑ g, Matrix.vecMulVec (clusterErrorScore X (e ω) cluster g)
          (clusterErrorScore X (e ω) cluster g)) a b) =
        fun ω => ∑ g, s g ω := by
    funext ω
    simp [s, Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hscore_sum : ∀ g,
      s g =
        fun ω =>
          ∑ i : ClusterIndex cluster g, ∑ j : ClusterIndex cluster g,
            (X i.1 a * X j.1 b) * (e ω i.1 * e ω j.1) := by
    intro g
    funext ω
    calc
      s g ω =
          (∑ i : ClusterIndex cluster g, X i.1 a * e ω i.1) *
            (∑ j : ClusterIndex cluster g, X j.1 b * e ω j.1) := by
          simp [s, clusterErrorScore_apply]
      _ = ∑ i : ClusterIndex cluster g, ∑ j : ClusterIndex cluster g,
            (X i.1 a * X j.1 b) * (e ω i.1 * e ω j.1) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
  rw [hleft]
  have hsum_g :
      μ[(fun ω => ∑ g, s g ω) | m] =ᵐ[μ] ∑ g, μ[s g | m] := by
    have hsum_repr :
        (fun ω => ∑ g, s g ω) = ∑ g, s g := by
      funext ω
      simp
    rw [hsum_repr]
    simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
      (s := Finset.univ) (f := s) (fun g _ => by simpa [s] using hscore_int g)
  have hcond_g : ∀ g,
      μ[s g | m] =ᵐ[μ]
        fun _ => ∑ i : ClusterIndex cluster g, ∑ j : ClusterIndex cluster g,
          (X i.1 a * X j.1 b) * Sigma g i j := by
    intro g
    let M : Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ :=
      Matrix.vecMulVec (fun i => X i.1 a) (fun j => X j.1 b)
    have hscore_quad :
        s g =
          fun ω => clusterError (e ω) cluster g ⬝ᵥ
            M *ᵥ clusterError (e ω) cluster g := by
      funext ω
      calc
        s g ω =
            ∑ i : ClusterIndex cluster g, ∑ j : ClusterIndex cluster g,
              (X i.1 a * X j.1 b) * (e ω i.1 * e ω j.1) := by
            exact congrFun (hscore_sum g) ω
        _ = clusterError (e ω) cluster g ⬝ᵥ
              M *ᵥ clusterError (e ω) cluster g := by
            simp [M, clusterError, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply,
              Finset.mul_sum, mul_left_comm, mul_comm]
    rw [hscore_quad]
    have hquad := condExp_quadratic_form_eq_sum
      (μ := μ) (m := m) (m₀ := m₀)
      M (fun ω => clusterError (e ω) cluster g) (Sigma g) hm
      (fun i j => by simpa [clusterError] using hee_int g i j)
      (fun i j => by simpa [clusterError] using hSigma g i j)
    refine hquad.trans ?_
    filter_upwards [] with ω
    simp [M, Matrix.vecMulVec_apply]
  refine hsum_g.trans ?_
  have hall : ∀ᵐ ω ∂μ, ∀ g,
      μ[s g | m] ω =
        ∑ i : ClusterIndex cluster g, ∑ j : ClusterIndex cluster g,
          (X i.1 a * X j.1 b) * Sigma g i j := by
    exact ae_all_iff.2 fun g => hcond_g g
  filter_upwards [hall] with ω hω
  calc
    ((∑ g, μ[s g | m]) : Ω → ℝ) ω =
        ∑ g, μ[s g | m] ω := by
          simp
    _ = ∑ g, ∑ i : ClusterIndex cluster g, ∑ j : ClusterIndex cluster g,
          (X i.1 a * X j.1 b) * Sigma g i j := by
          exact Finset.sum_congr rfl fun g _ => hω g
    _ = clusterCovarianceMiddle X cluster Sigma a b := by
          symm
          rw [clusterCovarianceMiddle_apply]
          refine Finset.sum_congr rfl ?_
          intro g _
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          ring

omit [DecidableEq k] in
/-- Matrix-valued conditional expectation of the infeasible clustered score middle. -/
theorem condExp_clusterErrorScoreMiddle_eq_clusterCovarianceMiddle
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ g (i j : ClusterIndex cluster g),
      Integrable (fun ω => e ω i.1 * e ω j.1) μ)
    (hSigma : ∀ g (i j : ClusterIndex cluster g),
      μ[fun ω => e ω i.1 * e ω j.1 | m] =ᵐ[μ] fun _ => Sigma g i j)
    (hscore_int : ∀ g a b,
      Integrable
        (fun ω =>
          clusterErrorScore X (e ω) cluster g a *
            clusterErrorScore X (e ω) cluster g b) μ) :
    μ[(fun ω => fun a b =>
      (∑ g, Matrix.vecMulVec (clusterErrorScore X (e ω) cluster g)
        (clusterErrorScore X (e ω) cluster g)) a b) | m] =ᵐ[μ]
      fun _ a b => clusterCovarianceMiddle X cluster Sigma a b := by
  let f : Ω → k → k → ℝ := fun ω a b =>
    (∑ g, Matrix.vecMulVec (clusterErrorScore X (e ω) cluster g)
      (clusterErrorScore X (e ω) cluster g)) a b
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro a
    refine Integrable.of_eval ?_
    intro b
    have hrepr :
        (fun ω => f ω a b) =
          fun ω => ∑ g,
            clusterErrorScore X (e ω) cluster g a *
              clusterErrorScore X (e ω) cluster g b := by
      funext ω
      simp [f, Matrix.sum_apply, Matrix.vecMulVec_apply]
    rw [hrepr]
    exact MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun g ω =>
        clusterErrorScore X (e ω) cluster g a *
          clusterErrorScore X (e ω) cluster g b)
      (fun g _ => hscore_int g a b)
  rw [Filter.EventuallyEq]
  change ∀ᵐ ω ∂μ, μ[f | m] ω = fun a b => clusterCovarianceMiddle X cluster Sigma a b
  have hcoord : ∀ a b : k, ∀ᵐ ω ∂μ,
      μ[f | m] ω a b = clusterCovarianceMiddle X cluster Sigma a b := by
    intro a b
    have hentry :
        μ[(fun ω => f ω a b) | m] =ᵐ[μ]
          fun _ => clusterCovarianceMiddle X cluster Sigma a b := by
      simpa [f] using
        condExp_clusterErrorScoreMiddle_entry_eq_clusterCovarianceMiddle
          (μ := μ) (m := m) (m₀ := m₀) X e cluster Sigma hm hee_int hSigma a b
          (fun g => hscore_int g a b)
    exact (condExp_apply_apply (m := m) (μ := μ) (f := f) hf_int a b).trans hentry
  have hall : ∀ᵐ ω ∂μ, ∀ a b : k,
      μ[f | m] ω a b = clusterCovarianceMiddle X cluster Sigma a b := by
    exact ae_all_iff.2 fun a => ae_all_iff.2 fun b => hcoord a b
  exact hall.mono fun ω hω => by
    funext a b
    exact hω a b

/-- Matrix-valued conditional expectation of the infeasible clustered score
sandwich. This is Hansen equation (4.47) for the true-error cluster scores. -/
theorem condExp_clusterErrorScoreSandwich_eq_olsClusterConditionalVarianceMatrix
    {G : Type*} [Fintype G] [DecidableEq G]
    (X : Matrix n k ℝ) (e : Ω → n → ℝ) (cluster : n → G)
    (Sigma : ∀ g, Matrix (ClusterIndex cluster g) (ClusterIndex cluster g) ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ g (i j : ClusterIndex cluster g),
      Integrable (fun ω => e ω i.1 * e ω j.1) μ)
    (hSigma : ∀ g (i j : ClusterIndex cluster g),
      μ[fun ω => e ω i.1 * e ω j.1 | m] =ᵐ[μ] fun _ => Sigma g i j)
    (hscore_int : ∀ g a b,
      Integrable
        (fun ω =>
          clusterErrorScore X (e ω) cluster g a *
            clusterErrorScore X (e ω) cluster g b) μ) :
    μ[(fun ω => fun a b =>
      (⅟ (Xᵀ * X) *
        (∑ g, Matrix.vecMulVec (clusterErrorScore X (e ω) cluster g)
          (clusterErrorScore X (e ω) cluster g)) *
        ⅟ (Xᵀ * X)) a b) | m] =ᵐ[μ]
      fun _ a b => olsClusterConditionalVarianceMatrix X cluster Sigma a b := by
  let A : Matrix k k ℝ := ⅟ (Xᵀ * X)
  let middle : Ω → Matrix k k ℝ := fun ω =>
    ∑ g, Matrix.vecMulVec (clusterErrorScore X (e ω) cluster g)
      (clusterErrorScore X (e ω) cluster g)
  let f : Ω → k → k → ℝ := fun ω a b => (A * middle ω * A) a b
  have hmiddle_int : ∀ c d : k, Integrable (fun ω => middle ω c d) μ := by
    intro c d
    have hrepr :
        (fun ω => middle ω c d) =
          fun ω => ∑ g,
            clusterErrorScore X (e ω) cluster g c *
              clusterErrorScore X (e ω) cluster g d := by
      funext ω
      simp [middle, Matrix.sum_apply, Matrix.vecMulVec_apply]
    rw [hrepr]
    exact MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun g ω =>
        clusterErrorScore X (e ω) cluster g c *
          clusterErrorScore X (e ω) cluster g d)
      (fun g _ => hscore_int g c d)
  have hmiddle_cond : ∀ c d : k,
      μ[(fun ω => middle ω c d) | m] =ᵐ[μ]
        fun _ => clusterCovarianceMiddle X cluster Sigma c d := by
    intro c d
    simpa [middle] using
      condExp_clusterErrorScoreMiddle_entry_eq_clusterCovarianceMiddle
        (μ := μ) (m := m) (m₀ := m₀) X e cluster Sigma hm hee_int hSigma c d
        (fun g => hscore_int g c d)
  have hentry : ∀ (ω : Ω) (a b : k),
      f ω a b =
        ∑ c, ∑ d, (A a c * A d b) * middle ω c d := by
    intro ω a b
    calc
      f ω a b =
          ∑ d, (∑ c, A a c * middle ω c d) * A d b := by
            simp [f, Matrix.mul_apply]
      _ = ∑ d, ∑ c, (A a c * middle ω c d) * A d b := by
            refine Finset.sum_congr rfl ?_
            intro d _
            rw [Finset.sum_mul]
      _ = ∑ c, ∑ d, (A a c * middle ω c d) * A d b := by
            rw [Finset.sum_comm]
      _ = ∑ c, ∑ d, (A a c * A d b) * middle ω c d := by
            refine Finset.sum_congr rfl ?_
            intro c _
            refine Finset.sum_congr rfl ?_
            intro d _
            ring
  have htarget_entry : ∀ a b : k,
      olsClusterConditionalVarianceMatrix X cluster Sigma a b =
        ∑ c, ∑ d, (A a c * A d b) * clusterCovarianceMiddle X cluster Sigma c d := by
    intro a b
    calc
      olsClusterConditionalVarianceMatrix X cluster Sigma a b =
          ∑ d, (∑ c, A a c * clusterCovarianceMiddle X cluster Sigma c d) * A d b := by
            simp [olsClusterConditionalVarianceMatrix, A, Matrix.mul_apply]
      _ = ∑ d, ∑ c, (A a c * clusterCovarianceMiddle X cluster Sigma c d) * A d b := by
            refine Finset.sum_congr rfl ?_
            intro d _
            rw [Finset.sum_mul]
      _ = ∑ c, ∑ d, (A a c * clusterCovarianceMiddle X cluster Sigma c d) * A d b := by
            rw [Finset.sum_comm]
      _ = ∑ c, ∑ d, (A a c * A d b) * clusterCovarianceMiddle X cluster Sigma c d := by
            refine Finset.sum_congr rfl ?_
            intro c _
            refine Finset.sum_congr rfl ?_
            intro d _
            ring
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro a
    refine Integrable.of_eval ?_
    intro b
    have hrepr :
        (fun ω => f ω a b) =
          fun ω => ∑ c, ∑ d, (A a c * A d b) * middle ω c d := by
      funext ω
      exact hentry ω a b
    rw [hrepr]
    exact MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun c ω => ∑ d, (A a c * A d b) * middle ω c d)
      (fun c _ =>
        MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun d ω => (A a c * A d b) * middle ω c d)
          (fun d _ => (hmiddle_int c d).const_mul (A a c * A d b)))
  rw [Filter.EventuallyEq]
  change ∀ᵐ ω ∂μ, μ[f | m] ω =
    fun a b => olsClusterConditionalVarianceMatrix X cluster Sigma a b
  have hcoord : ∀ a b : k, ∀ᵐ ω ∂μ,
      μ[f | m] ω a b = olsClusterConditionalVarianceMatrix X cluster Sigma a b := by
    intro a b
    have hrepr :
        (fun ω => f ω a b) =
          fun ω => ∑ c, ∑ d, (A a c * A d b) * middle ω c d := by
      funext ω
      exact hentry ω a b
    have hsum :
        μ[(fun ω => f ω a b) | m] =ᵐ[μ]
          fun _ => olsClusterConditionalVarianceMatrix X cluster Sigma a b := by
      rw [hrepr]
      have houter :
          μ[(fun ω => ∑ c, ∑ d, (A a c * A d b) * middle ω c d) | m] =ᵐ[μ]
            ∑ c, μ[(fun ω => ∑ d, (A a c * A d b) * middle ω c d) | m] := by
        have hsum_repr :
            (fun ω => ∑ c, ∑ d, (A a c * A d b) * middle ω c d) =
              ∑ c, fun ω => ∑ d, (A a c * A d b) * middle ω c d := by
          funext ω
          simp
        rw [hsum_repr]
        simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
          (s := Finset.univ)
          (f := fun c ω => ∑ d, (A a c * A d b) * middle ω c d)
          (fun c _ =>
            MeasureTheory.integrable_finset_sum (s := Finset.univ)
              (f := fun d ω => (A a c * A d b) * middle ω c d)
              (fun d _ => (hmiddle_int c d).const_mul (A a c * A d b)))
      have hinner : ∀ c,
          μ[(fun ω => ∑ d, (A a c * A d b) * middle ω c d) | m] =ᵐ[μ]
            fun _ => ∑ d, (A a c * A d b) *
              clusterCovarianceMiddle X cluster Sigma c d := by
        intro c
        have hinner_sum :
            μ[(fun ω => ∑ d, (A a c * A d b) * middle ω c d) | m] =ᵐ[μ]
              ∑ d, μ[(fun ω => (A a c * A d b) * middle ω c d) | m] := by
          have hsum_repr :
              (fun ω => ∑ d, (A a c * A d b) * middle ω c d) =
                ∑ d, fun ω => (A a c * A d b) * middle ω c d := by
            funext ω
            simp
          rw [hsum_repr]
          simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
            (s := Finset.univ)
            (f := fun d ω => (A a c * A d b) * middle ω c d)
            (fun d _ => (hmiddle_int c d).const_mul (A a c * A d b))
        have hcoord_smul : ∀ d,
            μ[(fun ω => (A a c * A d b) * middle ω c d) | m] =ᵐ[μ]
              fun _ => (A a c * A d b) *
                clusterCovarianceMiddle X cluster Sigma c d := by
          intro d
          refine (MeasureTheory.condExp_smul (μ := μ) (m := m)
            (A a c * A d b) (fun ω => middle ω c d)).trans ?_
          filter_upwards [hmiddle_cond c d] with ω hω
          simp [Pi.smul_apply, smul_eq_mul, hω]
        refine hinner_sum.trans ?_
        have hall : ∀ᵐ ω ∂μ, ∀ d,
            μ[(fun ω => (A a c * A d b) * middle ω c d) | m] ω =
              (A a c * A d b) * clusterCovarianceMiddle X cluster Sigma c d := by
          exact ae_all_iff.2 fun d => hcoord_smul d
        filter_upwards [hall] with ω hω
        calc
          ((∑ d, μ[(fun ω => (A a c * A d b) * middle ω c d) | m]) : Ω → ℝ) ω =
              ∑ d, μ[(fun ω => (A a c * A d b) * middle ω c d) | m] ω := by
                simp
          _ = ∑ d, (A a c * A d b) *
                clusterCovarianceMiddle X cluster Sigma c d := by
                exact Finset.sum_congr rfl fun d _ => hω d
      refine houter.trans ?_
      have hall : ∀ᵐ ω ∂μ, ∀ c,
          μ[(fun ω => ∑ d, (A a c * A d b) * middle ω c d) | m] ω =
            ∑ d, (A a c * A d b) * clusterCovarianceMiddle X cluster Sigma c d := by
        exact ae_all_iff.2 fun c => hinner c
      filter_upwards [hall] with ω hω
      calc
        ((∑ c, μ[(fun ω => ∑ d, (A a c * A d b) * middle ω c d) | m]) :
            Ω → ℝ) ω =
            ∑ c, μ[(fun ω => ∑ d, (A a c * A d b) * middle ω c d) | m] ω := by
              simp
        _ = ∑ c, ∑ d, (A a c * A d b) *
              clusterCovarianceMiddle X cluster Sigma c d := by
              exact Finset.sum_congr rfl fun c _ => hω c
        _ = olsClusterConditionalVarianceMatrix X cluster Sigma a b := by
              exact (htarget_entry a b).symm
    exact (condExp_apply_apply (m := m) (μ := μ) (f := f) hf_int a b).trans hsum
  have hall : ∀ᵐ ω ∂μ, ∀ a b : k,
      μ[f | m] ω a b = olsClusterConditionalVarianceMatrix X cluster Sigma a b := by
    exact ae_all_iff.2 fun a => ae_all_iff.2 fun b => hcoord a b
  filter_upwards [hall] with ω hω
  funext a b
  exact hω a b

/-- Matrix-valued conditional expectation of HC2 under homoskedastic second moments.

The rowwise leverage adjustment exactly removes the homoskedastic residual shrinkage, so the
conditional expectation is the usual homoskedastic covariance matrix. -/
theorem condExp_olsHuberWhiteHC2VarianceEstimator_eq_homoskedastic
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (σ2 : ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_homo : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => σ2 * (1 : Matrix n n ℝ) r s)
    (hlev_ne : ∀ i, 1 - hatMatrix X i i ≠ 0)
    (hhc2_int : ∀ i,
      Integrable
        (fun ω => (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e ω) i ^ 2) μ) :
    μ[(fun ω => fun a b =>
        olsHuberWhiteHC2VarianceEstimator X (X *ᵥ β + e ω) a b) | m]
      =ᵐ[μ] fun _ a b => olsConditionalVarianceMatrix X (σ2 • (1 : Matrix n n ℝ)) a b := by
  let z : Ω → n → ℝ := fun ω i =>
    (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e ω) i ^ 2
  have hz : ∀ i, μ[fun ω => z ω i | m] =ᵐ[μ] fun _ => σ2 := by
    intro i
    simpa [z] using
      condExp_HC2_adjusted_annihilator_row_sq_eq_sigmaSq
        (μ := μ) (m := m) X e σ2 i hm hee_int hee_homo (hlev_ne i)
  have hdiag :=
    condExp_olsConditionalVarianceMatrix_diagonal_eq
      (μ := μ) (m := m) X z (fun _ : n => σ2) hhc2_int hz
  have hconstdiag : Matrix.diagonal (fun _ : n => σ2) = σ2 • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij, smul_eq_mul]
  simpa [z, olsHuberWhiteHC2VarianceEstimator_linear_model, hconstdiag] using hdiag

/-- Matrix-valued conditional expectation of HC3 under homoskedastic second moments.

Relative to HC2, HC3 retains one extra inverse-leverage factor in each diagonal entry. -/
theorem condExp_olsHuberWhiteHC3VarianceEstimator_eq_homoskedastic_inflated
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (σ2 : ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_homo : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => σ2 * (1 : Matrix n n ℝ) r s)
    (hlev_ne : ∀ i, 1 - hatMatrix X i i ≠ 0)
    (hhc3_int : ∀ i,
      Integrable
        (fun ω => ((1 - hatMatrix X i i)⁻¹) ^ 2 *
          (annihilatorMatrix X *ᵥ e ω) i ^ 2) μ) :
    μ[(fun ω => fun a b =>
        olsHuberWhiteHC3VarianceEstimator X (X *ᵥ β + e ω) a b) | m]
      =ᵐ[μ] fun _ a b =>
        olsConditionalVarianceMatrix X
          (Matrix.diagonal fun i => σ2 * (1 - hatMatrix X i i)⁻¹) a b := by
  let z : Ω → n → ℝ := fun ω i =>
    ((1 - hatMatrix X i i)⁻¹) ^ 2 * (annihilatorMatrix X *ᵥ e ω) i ^ 2
  let d : n → ℝ := fun i => σ2 * (1 - hatMatrix X i i)⁻¹
  have hz : ∀ i, μ[fun ω => z ω i | m] =ᵐ[μ] fun _ => d i := by
    intro i
    simpa [z, d] using
      condExp_HC3_adjusted_annihilator_row_sq_eq_sigmaSq_mul_inv
        (μ := μ) (m := m) X e σ2 i hm hee_int hee_homo (hlev_ne i)
  have hdiag :=
    condExp_olsConditionalVarianceMatrix_diagonal_eq
      (μ := μ) (m := m) X z d hhc3_int hz
  simpa [z, d, olsHuberWhiteHC3VarianceEstimator_linear_model, Matrix.diagonal] using hdiag

/-- Matrix-valued conditional expectation of HC2 under diagonal heteroskedastic second moments. -/
theorem condExp_olsHuberWhiteHC2VarianceEstimator_eq_diagonal
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (σ2 : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_diag : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => (Matrix.diagonal σ2) r s)
    (hhc2_int : ∀ i,
      Integrable
        (fun ω => (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e ω) i ^ 2) μ) :
    μ[(fun ω => fun a b =>
        olsHuberWhiteHC2VarianceEstimator X (X *ᵥ β + e ω) a b) | m]
      =ᵐ[μ] fun _ a b =>
        olsConditionalVarianceMatrix X
          (Matrix.diagonal fun i =>
            (1 - hatMatrix X i i)⁻¹ *
              ∑ r, annihilatorMatrix X i r * annihilatorMatrix X i r * σ2 r) a b := by
  let z : Ω → n → ℝ := fun ω i =>
    (1 - hatMatrix X i i)⁻¹ * (annihilatorMatrix X *ᵥ e ω) i ^ 2
  let d : n → ℝ := fun i =>
    (1 - hatMatrix X i i)⁻¹ *
      ∑ r, annihilatorMatrix X i r * annihilatorMatrix X i r * σ2 r
  have hz : ∀ i, μ[fun ω => z ω i | m] =ᵐ[μ] fun _ => d i := by
    intro i
    simpa [z, d] using
      condExp_HC2_adjusted_annihilator_row_sq_eq_diagonal
        (μ := μ) (m := m) X e σ2 i hm hee_int hee_diag
  have hdiag :=
    condExp_olsConditionalVarianceMatrix_diagonal_eq
      (μ := μ) (m := m) X z d hhc2_int hz
  simpa [z, d, olsHuberWhiteHC2VarianceEstimator_linear_model, Matrix.diagonal] using hdiag

/-- Matrix-valued conditional expectation of HC3 under diagonal heteroskedastic second moments. -/
theorem condExp_olsHuberWhiteHC3VarianceEstimator_eq_diagonal
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (σ2 : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ r s, Integrable (fun ω => e ω r * e ω s) μ)
    (hee_diag : ∀ r s,
      μ[fun ω => e ω r * e ω s | m] =ᵐ[μ]
        fun _ => (Matrix.diagonal σ2) r s)
    (hhc3_int : ∀ i,
      Integrable
        (fun ω => ((1 - hatMatrix X i i)⁻¹) ^ 2 *
          (annihilatorMatrix X *ᵥ e ω) i ^ 2) μ) :
    μ[(fun ω => fun a b =>
        olsHuberWhiteHC3VarianceEstimator X (X *ᵥ β + e ω) a b) | m]
      =ᵐ[μ] fun _ a b =>
        olsConditionalVarianceMatrix X
          (Matrix.diagonal fun i =>
            ((1 - hatMatrix X i i)⁻¹) ^ 2 *
              ∑ r, annihilatorMatrix X i r * annihilatorMatrix X i r * σ2 r) a b := by
  let z : Ω → n → ℝ := fun ω i =>
    ((1 - hatMatrix X i i)⁻¹) ^ 2 * (annihilatorMatrix X *ᵥ e ω) i ^ 2
  let d : n → ℝ := fun i =>
    ((1 - hatMatrix X i i)⁻¹) ^ 2 *
      ∑ r, annihilatorMatrix X i r * annihilatorMatrix X i r * σ2 r
  have hz : ∀ i, μ[fun ω => z ω i | m] =ᵐ[μ] fun _ => d i := by
    intro i
    simpa [z, d] using
      condExp_HC3_adjusted_annihilator_row_sq_eq_diagonal
        (μ := μ) (m := m) X e σ2 i hm hee_int hee_diag
  have hdiag :=
    condExp_olsConditionalVarianceMatrix_diagonal_eq
      (μ := μ) (m := m) X z d hhc3_int hz
  simpa [z, d, olsHuberWhiteHC3VarianceEstimator_linear_model, Matrix.diagonal] using hdiag

/-- Private proof engine for Hansen (4.25): with diagonal conditional second moments,
the quadratic-form double sum is the trace of `M D`. -/
private theorem sum_quadratic_diagonal_eq_trace_mul
    (M : Matrix n n ℝ) [DecidableEq n] (σ2 : n → ℝ) :
    (∑ i, ∑ j, M i j * (Matrix.diagonal σ2) i j) =
      Matrix.trace (M * Matrix.diagonal σ2) := by
  classical
  rw [Matrix.trace]
  calc
    (∑ i, ∑ j, M i j * (Matrix.diagonal σ2) i j) =
        ∑ i, M i i * σ2 i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [hji.symm]
          · intro hi
            simp at hi
    _ = ∑ i, (M * Matrix.diagonal σ2) i i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Matrix.mul_apply, Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            simp [hji]
          · intro hi
            simp at hi

/-- Hansen equation (4.25): under diagonal heteroskedastic conditional second moments,
`E[σ̂² | X] = n⁻¹ tr(MD)` where `M` is the annihilator matrix and `D` is the
diagonal matrix of conditional error variances. -/
theorem ols_condExp_sigmaSqHat_eq_inv_card_trace_diagonal
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (σ2 : n → ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i j, Integrable (fun ω => e ω i * e ω j) μ)
    (hD : ∀ i j,
      μ[fun ω => e ω i * e ω j | m] =ᵐ[μ]
        fun _ => (Matrix.diagonal σ2) i j) :
    μ[fun ω => olsSigmaSqHat X (X *ᵥ β + e ω) | m]
      =ᵐ[μ]
        fun _ => (Fintype.card n : ℝ)⁻¹ *
          Matrix.trace (annihilatorMatrix X * Matrix.diagonal σ2) := by
  let M : Matrix n n ℝ := annihilatorMatrix X
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  have hrewrite : (fun ω => olsSigmaSqHat X (X *ᵥ β + e ω)) =
      fun ω => c * (e ω ⬝ᵥ M *ᵥ e ω) := by
    funext ω
    simp [c, M, olsSigmaSqHat_linear_model_quadratic_form]
  rw [hrewrite]
  have hscale : μ[(fun ω => c * (e ω ⬝ᵥ M *ᵥ e ω)) | m] =ᵐ[μ]
      fun ω => c * μ[fun ω => e ω ⬝ᵥ M *ᵥ e ω | m] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul (μ := μ) (m := m) c
        (fun ω => e ω ⬝ᵥ M *ᵥ e ω))
  have hquad := condExp_quadratic_form_eq_sum (μ := μ) (m := m) (m₀ := m₀)
    M e (Matrix.diagonal σ2) hm hee_int hD
  exact hscale.trans <| by
    filter_upwards [hquad] with ω hω
    simp [c, M, hω, sum_quadratic_diagonal_eq_trace_mul]

/-- Hansen equation (4.26): under a homoskedastic conditional second-moment assumption,
`E[s² | X] = σ²`.  The hypothesis `hee_homo` is a second-moment condition on
`E[eᵢeⱼ | m]`; with conditional mean zero it specializes to the usual conditional
variance/covariance statement. -/
theorem ols_condExp_residualVarianceEstimator_eq_sigmaSq
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (σ2 : ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i j, Integrable (fun ω => e ω i * e ω j) μ)
    (hee_homo : ∀ i j,
      μ[fun ω => e ω i * e ω j | m] =ᵐ[μ]
        fun _ => σ2 * (1 : Matrix n n ℝ) i j)
    (h_df : (Fintype.card n : ℝ) - Fintype.card k ≠ 0) :
    μ[fun ω => olsResidualVarianceEstimator X (X *ᵥ β + e ω) | m]
      =ᵐ[μ] fun _ => σ2 := by
  let M : Matrix n n ℝ := annihilatorMatrix X
  let df : ℝ := (Fintype.card n : ℝ) - Fintype.card k
  have hrewrite : (fun ω => olsResidualVarianceEstimator X (X *ᵥ β + e ω)) =
      fun ω => (e ω ⬝ᵥ M *ᵥ e ω) / df := by
    funext ω
    simp [M, df, olsResidualVarianceEstimator_linear_model_quadratic_form]
  rw [hrewrite]
  have hscale : μ[(fun ω => (e ω ⬝ᵥ M *ᵥ e ω) / df) | m] =ᵐ[μ]
      fun ω => df⁻¹ * μ[fun ω => e ω ⬝ᵥ M *ᵥ e ω | m] ω := by
    have hdiv : (fun ω => (e ω ⬝ᵥ M *ᵥ e ω) / df) =
        (fun ω => df⁻¹ • (e ω ⬝ᵥ M *ᵥ e ω)) := by
      funext ω
      simp [div_eq_mul_inv, mul_comm]
    rw [hdiv]
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul (μ := μ) (m := m) df⁻¹
        (fun ω => e ω ⬝ᵥ M *ᵥ e ω))
  have hquad : μ[fun ω => e ω ⬝ᵥ M *ᵥ e ω | m] =ᵐ[μ]
      fun _ => σ2 * df := by
    have hsum := condExp_quadratic_form_eq_sum (μ := μ) (m := m) (m₀ := m₀)
      M e (σ2 • (1 : Matrix n n ℝ)) hm hee_int
      (fun i j => by
        simpa [Pi.smul_apply, smul_eq_mul] using hee_homo i j)
    refine hsum.trans ?_
    filter_upwards [] with ω
    dsimp [df]
    calc
      (∑ i, ∑ j, M i j * (σ2 • (1 : Matrix n n ℝ)) i j)
          = ∑ i, ∑ j, M i j * (σ2 * (1 : Matrix n n ℝ) i j) := by simp [smul_eq_mul]
      _ = σ2 * Matrix.trace M := sum_quadratic_homoskedastic_eq_trace M σ2
      _ = σ2 * ((Fintype.card n : ℝ) - Fintype.card k) := by
        simp [M, annihilatorMatrix_trace]
  exact hscale.trans <| by
    filter_upwards [hquad] with ω hω
    rw [hω]
    dsimp [df] at h_df ⊢
    field_simp [h_df]

/-- Unconditional unbiasedness of `s²` obtained by integrating the conditional statement. -/
theorem ols_integral_residualVarianceEstimator_eq_sigmaSq
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (σ2 : ℝ)
    [DecidableEq n] [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i j, Integrable (fun ω => e ω i * e ω j) μ)
    (hee_homo : ∀ i j,
      μ[fun ω => e ω i * e ω j | m] =ᵐ[μ]
        fun _ => σ2 * (1 : Matrix n n ℝ) i j)
    (h_df : (Fintype.card n : ℝ) - Fintype.card k ≠ 0)
    (h_int : Integrable (fun ω => olsResidualVarianceEstimator X (X *ᵥ β + e ω)) μ) :
    ∫ ω, olsResidualVarianceEstimator X (X *ᵥ β + e ω) ∂μ = σ2 := by
  have _hf_int : Integrable (fun ω => olsResidualVarianceEstimator X (X *ᵥ β + e ω)) μ := h_int
  calc
    ∫ ω, olsResidualVarianceEstimator X (X *ᵥ β + e ω) ∂μ =
        ∫ ω, μ[fun ω => olsResidualVarianceEstimator X (X *ᵥ β + e ω) | m] ω ∂μ := by
      symm
      exact MeasureTheory.integral_condExp (μ := μ) (m := m) (m₀ := m₀)
        (f := fun ω => olsResidualVarianceEstimator X (X *ᵥ β + e ω)) hm
    _ = ∫ _ω, σ2 ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      exact ols_condExp_residualVarianceEstimator_eq_sigmaSq
        (μ := μ) (m := m) X β e σ2 hm hee_int hee_homo h_df
    _ = σ2 := by simp

/-- Componentwise conditional unbiasedness of OLS under conditional mean-zero errors. -/
theorem ols_condExp_coordinate_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (j : k)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    μ[fun ω => olsBeta X (X *ᵥ β + e ω) j | m] =ᵐ[μ] fun _ => β j := by
  let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
  have hrepr : (fun ω => olsBeta X (X *ᵥ β + e ω) j) =
      fun ω => β j + ∑ i, w j i * e ω i := by
    funext ω
    simp [w, Matrix.mulVec, dotProduct]
  rw [hrepr]
  have hsum_int : Integrable (fun ω => ∑ i, w j i * e ω i) μ := by
    simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => w j i * e ω i)
      (fun i _ => (he_int i).const_mul (w j i))
  have hconst : μ[(fun _ : Ω => β j) | m] = fun _ => β j := by
    simpa using MeasureTheory.condExp_const (μ := μ) (m := m) (m₀ := m₀) hm (β j)
  have hsum_repr : (fun ω => ∑ i, w j i * e ω i) = ∑ i, fun ω => w j i * e ω i := by
    funext ω
    simp
  have hsum_ce : μ[(fun ω => ∑ i, w j i * e ω i) | m] =ᵐ[μ]
      ∑ i, μ[(fun ω => w j i * e ω i) | m] := by
    rw [hsum_repr]
    simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
      (s := Finset.univ) (f := fun i ω => w j i * e ω i)
      (fun i _ => (he_int i).const_mul (w j i))
  have hsum_smul : (∑ i, μ[(fun ω => w j i * e ω i) | m]) =ᵐ[μ]
      ∑ i, (fun ω => w j i * μ[fun ω => e ω i | m] ω) := by
    classical
    refine Finset.induction_on (Finset.univ : Finset n) ?_ ?_
    · simp
    · intro a s ha ih
      have ha' : μ[(fun ω => w j a * e ω a) | m] =ᵐ[μ]
          (fun ω => w j a * μ[fun ω => e ω a | m] ω) := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (MeasureTheory.condExp_smul (μ := μ) (m := m) (w j a) (fun ω => e ω a))
      simpa [Finset.sum_insert, ha] using ha'.add ih
  have hsum_zero : (∑ i, (fun ω => w j i * μ[fun ω => e ω i | m] ω)) =ᵐ[μ] 0 := by
    classical
    refine Finset.induction_on (Finset.univ : Finset n) ?_ ?_
    · simp
    · intro a s ha ih
      have hzeroa : (fun ω => w j a * μ[fun ω => e ω a | m] ω) =ᵐ[μ] 0 := by
        filter_upwards [he_zero a] with ω hω
        simp [hω]
      simpa [Finset.sum_insert, ha] using hzeroa.add ih
  have hsum_final : μ[(fun ω => ∑ i, w j i * e ω i) | m] =ᵐ[μ] 0 :=
    hsum_ce.trans (hsum_smul.trans hsum_zero)
  calc
    μ[(fun ω => β j + ∑ i, w j i * e ω i) | m]
        =ᵐ[μ] μ[(fun _ : Ω => β j) | m] + μ[(fun ω => ∑ i, w j i * e ω i) | m] := by
          simpa using MeasureTheory.condExp_add (μ := μ) (m := m)
            (integrable_const (β j)) hsum_int
    _ =ᵐ[μ] (fun _ => β j) + 0 := by
          rw [hconst]
          exact Filter.EventuallyEq.add Filter.EventuallyEq.rfl hsum_final
    _ =ᵐ[μ] fun _ => β j := by simp

/-- Componentwise unconditional unbiasedness from the conditional mean-zero assumption. -/
theorem ols_integral_coordinate_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (j : k)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ = β j := by
  calc
    ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ = ∫ ω, μ[fun ω => olsBeta X (X *ᵥ β + e ω) j | m] ω ∂μ := by
      symm
      exact MeasureTheory.integral_condExp (μ := μ) (m := m) (m₀ := m₀)
        (f := fun ω => olsBeta X (X *ᵥ β + e ω) j) hm
    _ = ∫ ω, β j ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      exact ols_condExp_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero
    _ = β j := by simp

/-- Uniform coordinatewise conditional unbiasedness of OLS. -/
theorem ols_condExp_all_coordinates_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    ∀ j, μ[fun ω => olsBeta X (X *ᵥ β + e ω) j | m] =ᵐ[μ] fun _ => β j := by
  intro j
  exact ols_condExp_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero

/-- Vector-valued conditional unbiasedness of OLS. -/
theorem ols_condExp_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    μ[(fun ω => olsBeta X (X *ᵥ β + e ω)) | m] =ᵐ[μ] fun _ => β := by
  let f : Ω → k → ℝ := fun ω => olsBeta X (X *ᵥ β + e ω)
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
    have hrepr : (fun ω => f ω j) = fun ω => β j + ∑ i, w j i * e ω i := by
      funext ω
      simp [f, olsBeta_linear_decomposition, w, Matrix.mulVec, dotProduct]
    rw [hrepr]
    have hsum_int : Integrable (fun ω => ∑ i, w j i * e ω i) μ := by
      simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
        (f := fun i ω => w j i * e ω i)
        (fun i _ => (he_int i).const_mul (w j i))
    exact (integrable_const (β j)).add hsum_int
  rw [Filter.EventuallyEq]
  change ∀ᵐ ω ∂μ, μ[f | m] ω = β
  have hcoord : ∀ j : k, ∀ᵐ ω ∂μ, μ[f | m] ω j = β j := by
    intro j
    exact (condExp_apply (m := m) (μ := μ) (f := f) hf_int j).trans <|
      ols_condExp_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero
  have hall : ∀ᵐ ω ∂μ, ∀ j : k, μ[f | m] ω j = β j := by
    exact ae_all_iff.2 hcoord
  exact hall.mono fun ω hω => by
    funext j
    exact hω j

/-- Uniform coordinatewise unconditional unbiasedness of OLS. -/
theorem ols_integral_all_coordinates_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    ∀ j, ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ = β j := by
  intro j
  exact ols_integral_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero

/-- Vector-valued unconditional unbiasedness of OLS. -/
theorem ols_integral_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    ∫ ω, olsBeta X (X *ᵥ β + e ω) ∂μ = β := by
  let f : Ω → k → ℝ := fun ω => olsBeta X (X *ᵥ β + e ω)
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
    have hrepr : (fun ω => f ω j) = fun ω => β j + ∑ i, w j i * e ω i := by
      funext ω
      simp [f, olsBeta_linear_decomposition, w, Matrix.mulVec, dotProduct]
    rw [hrepr]
    have hsum_int : Integrable (fun ω => ∑ i, w j i * e ω i) μ := by
      simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
        (f := fun i ω => w j i * e ω i)
        (fun i _ => (he_int i).const_mul (w j i))
    exact (integrable_const (β j)).add hsum_int
  funext j
  calc
    (∫ ω, olsBeta X (X *ᵥ β + e ω) ∂μ) j = ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ := by
      simpa [f] using integral_apply (μ := μ) (f := f) hf_int j
    _ = β j := ols_integral_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero

/-- Coordinatewise conditional covariance bridge for OLS. -/
theorem ols_condExp_centered_mul_eq_variance_entry
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (D : Matrix n n ℝ) (j l : k)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i r, Integrable (fun ω => e ω i * e ω r) μ)
    (hD : ∀ i r, μ[fun ω => e ω i * e ω r | m] =ᵐ[μ] fun _ => D i r) :
    μ[fun ω => (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l) | m] =ᵐ[μ]
      fun _ => olsConditionalVarianceMatrix X D j l := by
  let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
  have hj : (fun ω => olsBeta X (X *ᵥ β + e ω) j - β j) = fun ω => ∑ i, w j i * e ω i := by
    funext ω
    simp [w, Matrix.mulVec, dotProduct]
  have hl : (fun ω => olsBeta X (X *ᵥ β + e ω) l - β l) = fun ω => ∑ r, w l r * e ω r := by
    funext ω
    simp [w, Matrix.mulVec, dotProduct]
  have hprod :
      (fun ω => (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l)) =
      fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
    funext ω
    rw [show olsBeta X (X *ᵥ β + e ω) j - β j = ∑ i, w j i * e ω i by exact congrFun hj ω]
    rw [show olsBeta X (X *ᵥ β + e ω) l - β l = ∑ r, w l r * e ω r by exact congrFun hl ω]
    calc
      (∑ i, w j i * e ω i) * (∑ r, w l r * e ω r)
          = ∑ r, (∑ i, w j i * e ω i) * (w l r * e ω r) := by rw [Finset.mul_sum]
      _ = ∑ r, ∑ i, (w j i * e ω i) * (w l r * e ω r) := by simp [Finset.sum_mul]
      _ = ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
            rw [Finset.sum_comm]
            simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hprod]
  have hint : Integrable (fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r)) μ := by
    simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => ∑ r, (w j i * w l r) * (e ω i * e ω r))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
          (fun r _ => (hee_int i r).const_mul (w j i * w l r)))
  have hsum1 :
      μ[(fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m] =ᵐ[μ]
        ∑ i, μ[(fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m] := by
    have hrepr :
        (fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r)) =
          ∑ i, fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
      funext ω
      simp
    rw [hrepr]
    simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
      (s := Finset.univ)
      (f := fun i ω => ∑ r, (w j i * w l r) * (e ω i * e ω r))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
          (fun r _ => (hee_int i r).const_mul (w j i * w l r)))
  have hsum2 :
      (∑ i, μ[(fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m]) =ᵐ[μ]
        ∑ i, ∑ r, (fun ω => (w j i * w l r) * D i r) := by
    have hinner : ∀ i,
        μ[(fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m] =ᵐ[μ]
          ∑ r, μ[(fun ω => (w j i * w l r) * (e ω i * e ω r)) | m] := by
      intro i
      have hrepr :
          (fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) =
            ∑ r, fun ω => (w j i * w l r) * (e ω i * e ω r) := by
        funext ω
        simp
      rw [hrepr]
      simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
        (s := Finset.univ)
        (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
        (fun r _ => (hee_int i r).const_mul (w j i * w l r))
    have hcoord : ∀ i r,
        μ[(fun ω => (w j i * w l r) * (e ω i * e ω r)) | m] =ᵐ[μ]
          (fun ω => (w j i * w l r) * D i r) := by
      intro i r
      refine (MeasureTheory.condExp_smul (μ := μ) (m := m) (w j i * w l r)
        (fun ω => e ω i * e ω r)).trans ?_
      filter_upwards [hD i r] with ω hω
      simp [Pi.smul_apply, smul_eq_mul, hω]
    have hall1 : ∀ᵐ ω ∂μ, ∀ i, μ[(fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m] ω =
        ∑ r, μ[(fun ω => (w j i * w l r) * (e ω i * e ω r)) | m] ω := by
      exact ae_all_iff.2 fun i => by simpa [Filter.EventuallyEq] using hinner i
    have hall2 : ∀ᵐ ω ∂μ, ∀ i, ∀ r,
        μ[(fun ω => (w j i * w l r) * (e ω i * e ω r)) | m] ω = (w j i * w l r) * D i r := by
      exact ae_all_iff.2 fun i => ae_all_iff.2 fun r => hcoord i r
    filter_upwards [hall1, hall2] with ω h1 h2
    simp [h1, h2]
  have hvar_repr : olsConditionalVarianceMatrix X D = w * D * wᵀ := by
    unfold olsConditionalVarianceMatrix w
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, inv_gram_transpose]
    simp [Matrix.mul_assoc]
  have hentry : olsConditionalVarianceMatrix X D j l = ∑ i, ∑ r, (w j i * w l r) * D i r := by
    rw [hvar_repr, Matrix.mul_apply]
    calc
      ∑ t, (w * D) j t * wᵀ t l = ∑ t, (w * D) j t * w l t := by
        simp [Matrix.transpose_apply]
      _ = ∑ t, (∑ r, w j r * D r t) * w l t := by
        simp [Matrix.mul_apply]
      _ = ∑ t, ∑ r, w j r * D r t * w l t := by
        simp [Finset.sum_mul, mul_assoc]
      _ = ∑ r, ∑ t, w j r * D r t * w l t := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ r, (w j i * w l r) * D i r := by
        simp [mul_assoc, mul_comm]
  exact (hsum1.trans hsum2).trans <| by
    filter_upwards [] with ω
    simp [hentry]

/-- Matrix-valued conditional covariance bridge for OLS. -/
theorem ols_condExp_centered_mul_eq_variance_matrix
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (D : Matrix n n ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i r, Integrable (fun ω => e ω i * e ω r) μ)
    (hD : ∀ i r, μ[fun ω => e ω i * e ω r | m] =ᵐ[μ] fun _ => D i r) :
    μ[(fun ω => fun j l =>
      (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l)) | m] =ᵐ[μ]
      fun _ => olsConditionalVarianceMatrix X D := by
  let f : Ω → k → k → ℝ := fun ω j l =>
    (olsBeta X (X *ᵥ β + e ω) j - β j) *
      (olsBeta X (X *ᵥ β + e ω) l - β l)
  have hf_eval_int : ∀ j l, Integrable (fun ω => f ω j l) μ := by
    intro j l
    let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
    have hrepr :
        (fun ω => f ω j l) =
          fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
      funext ω
      dsimp [f]
      rw [show olsBeta X (X *ᵥ β + e ω) j - β j = ∑ i, w j i * e ω i by
          simp [w, Matrix.mulVec, dotProduct]]
      rw [show olsBeta X (X *ᵥ β + e ω) l - β l = ∑ r, w l r * e ω r by
          simp [w, Matrix.mulVec, dotProduct]]
      calc
        (∑ i, w j i * e ω i) * (∑ r, w l r * e ω r)
            = ∑ r, (∑ i, w j i * e ω i) * (w l r * e ω r) := by rw [Finset.mul_sum]
        _ = ∑ r, ∑ i, (w j i * e ω i) * (w l r * e ω r) := by simp [Finset.sum_mul]
        _ = ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
              rw [Finset.sum_comm]
              simp [mul_assoc, mul_left_comm, mul_comm]
    rw [hrepr]
    simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => ∑ r, (w j i * w l r) * (e ω i * e ω r))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
          (fun r _ => (hee_int i r).const_mul (w j i * w l r)))
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    refine Integrable.of_eval ?_
    intro l
    exact hf_eval_int j l
  rw [Filter.EventuallyEq]
  change ∀ᵐ ω ∂μ, μ[f | m] ω = olsConditionalVarianceMatrix X D
  have hcoord : ∀ j l : k, ∀ᵐ ω ∂μ, μ[f | m] ω j l = olsConditionalVarianceMatrix X D j l := by
    intro j l
    exact (condExp_apply_apply (m := m) (μ := μ) (f := f) hf_int j l).trans <|
      ols_condExp_centered_mul_eq_variance_entry
        (μ := μ) (m := m) X β e D j l hm hee_int hD
  have hall : ∀ᵐ ω ∂μ, ∀ j l : k, μ[f | m] ω j l = olsConditionalVarianceMatrix X D j l := by
    exact ae_all_iff.2 fun j => ae_all_iff.2 fun l => hcoord j l
  exact hall.mono fun ω hω => by
    funext j l
    exact hω j l

/-- Matrix-valued unconditional covariance bridge for OLS. -/
theorem ols_integral_centered_mul_eq_variance_matrix
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (D : Matrix n n ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i r, Integrable (fun ω => e ω i * e ω r) μ)
    (hD : ∀ i r, μ[fun ω => e ω i * e ω r | m] =ᵐ[μ] fun _ => D i r) :
    ∫ ω, (fun j l =>
      (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l)) ∂μ =
      olsConditionalVarianceMatrix X D := by
  let f : Ω → k → k → ℝ := fun ω j l =>
    (olsBeta X (X *ᵥ β + e ω) j - β j) *
      (olsBeta X (X *ᵥ β + e ω) l - β l)
  have hf_eval_int : ∀ j l, Integrable (fun ω => f ω j l) μ := by
    intro j l
    let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
    have hrepr :
        (fun ω => f ω j l) =
          fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
      funext ω
      dsimp [f]
      rw [show olsBeta X (X *ᵥ β + e ω) j - β j = ∑ i, w j i * e ω i by
          simp [w, Matrix.mulVec, dotProduct]]
      rw [show olsBeta X (X *ᵥ β + e ω) l - β l = ∑ r, w l r * e ω r by
          simp [w, Matrix.mulVec, dotProduct]]
      calc
        (∑ i, w j i * e ω i) * (∑ r, w l r * e ω r)
            = ∑ r, (∑ i, w j i * e ω i) * (w l r * e ω r) := by rw [Finset.mul_sum]
        _ = ∑ r, ∑ i, (w j i * e ω i) * (w l r * e ω r) := by simp [Finset.sum_mul]
        _ = ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
              rw [Finset.sum_comm]
              simp [mul_assoc, mul_left_comm, mul_comm]
    rw [hrepr]
    simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => ∑ r, (w j i * w l r) * (e ω i * e ω r))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
          (fun r _ => (hee_int i r).const_mul (w j i * w l r)))
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    refine Integrable.of_eval ?_
    intro l
    exact hf_eval_int j l
  funext j l
  calc
    (∫ ω, f ω ∂μ) j l = ∫ ω, f ω j l ∂μ := by
      simpa using integral_apply_apply (μ := μ) (f := f) hf_int j l
    _ = olsConditionalVarianceMatrix X D j l := by
      calc
        ∫ ω, f ω j l ∂μ = ∫ ω, μ[(fun ω => f ω j l) | m] ω ∂μ := by
          symm
          exact MeasureTheory.integral_condExp (μ := μ) (m := m) (m₀ := m₀)
            (f := fun ω => f ω j l) hm
        _ = ∫ ω, olsConditionalVarianceMatrix X D j l ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          simpa [f] using
            ols_condExp_centered_mul_eq_variance_entry
              (μ := μ) (m := m) X β e D j l hm hee_int hD
        _ = olsConditionalVarianceMatrix X D j l := by simp

end ConditionalUnbiasedness

/-- Generalized least squares estimator with weight matrix `Ω⁻¹`. -/
noncomputable def glsBeta
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)] : k → ℝ :=
  (⅟ (Xᵀ * ⅟Ω * X)) *ᵥ (Xᵀ *ᵥ ((⅟Ω) *ᵥ y))

/-- GLS equals the true coefficient plus the weighted projected error. -/
theorem glsBeta_linear_decomposition
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)] :
    glsBeta X Ω (X *ᵥ β + e) = β + (⅟ (Xᵀ * ⅟Ω * X)) *ᵥ (Xᵀ *ᵥ ((⅟Ω) *ᵥ e)) := by
  unfold glsBeta
  rw [Matrix.mulVec_add, Matrix.mulVec_add]
  have hmain : Xᵀ *ᵥ ((⅟Ω) *ᵥ (X *ᵥ β)) = (Xᵀ * ⅟Ω * X) *ᵥ β := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hmain]
  rw [Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec β (⅟ (Xᵀ * ⅟Ω * X)) (Xᵀ * ⅟Ω * X)]
  rw [invOf_mul_self]
  simp

/-- If the GLS-weighted error is orthogonal to the regressors, GLS recovers `β`. -/
theorem glsBeta_eq_of_weighted_regressors_orthogonal_error
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)]
    (he : Xᵀ *ᵥ ((⅟Ω) *ᵥ e) = 0) :
    glsBeta X Ω (X *ᵥ β + e) = β := by
  rw [glsBeta_linear_decomposition, he]
  simp

/-- Deterministic core of the generalized Gauss-Markov theorem: the weighted variance gap is
positive semidefinite. -/
theorem generalizedGaussMarkov_variance_gap_posSemidef
    (X A : Matrix n k ℝ) (Ω : Matrix n n ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)]
    (hΩ : Ω.PosSemidef)
    (hAX : Aᵀ * X = (1 : Matrix k k ℝ)) :
    (Aᵀ * Ω * A - ⅟ (Xᵀ * ⅟Ω * X)).PosSemidef := by
  let M : Matrix k k ℝ := ⅟ (Xᵀ * ⅟Ω * X)
  let C : Matrix k n ℝ := Aᵀ * Ω - M * Xᵀ
  have hXA : Xᵀ * A = (1 : Matrix k k ℝ) := by
    simpa using congrArg Matrix.transpose hAX
  have hΩsym : Ωᵀ = Ω := by
    simpa [Matrix.IsHermitian] using hΩ.1
  have hsymW : (Xᵀ * ⅟Ω * X)ᵀ = Xᵀ * ⅟Ω * X := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_invOf]
    simp [hΩsym, Matrix.mul_assoc]
  have hMtranspose : Mᵀ = M := by
    dsimp [M]
    rw [Matrix.transpose_invOf]
    simpa [hsymW] using congrArg Inv.inv hsymW
  have hCtranspose : Cᵀ = Ω * A - X * M := by
    dsimp [C]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    simp [hMtranspose, hΩsym]
  have hgap : C * ⅟Ω * Cᵀ = Aᵀ * Ω * A - M := by
    calc
      C * ⅟Ω * Cᵀ = ((Aᵀ * Ω - M * Xᵀ) * ⅟Ω) * (Ω * A - X * M) := by
        rw [hCtranspose, Matrix.mul_assoc]
      _ = (Aᵀ * Ω * ⅟Ω - M * Xᵀ * ⅟Ω) * (Ω * A - X * M) := by
        rw [Matrix.sub_mul]
      _ = (Aᵀ * Ω * ⅟Ω - M * Xᵀ * ⅟Ω) * (Ω * A)
            - (Aᵀ * Ω * ⅟Ω - M * Xᵀ * ⅟Ω) * (X * M) := by
        rw [Matrix.mul_sub]
      _ = (Aᵀ * Ω * ⅟Ω * (Ω * A) - M * Xᵀ * ⅟Ω * (Ω * A))
            - (Aᵀ * Ω * ⅟Ω * (X * M) - M * Xᵀ * ⅟Ω * (X * M)) := by
        rw [Matrix.sub_mul, Matrix.sub_mul]
      _ = (Aᵀ * Ω * A - M) - (Aᵀ * (X * M) - M * (Xᵀ * (⅟Ω * (X * M)))) := by
        simp [M, hXA, Matrix.mul_assoc]
      _ = (Aᵀ * Ω * A - M) - (M - M) := by
        have hAXM : Aᵀ * (X * M) = M := by
          calc
            Aᵀ * (X * M) = (Aᵀ * X) * M := by rw [Matrix.mul_assoc]
            _ = M := by simp [hAX]
        have hMXM : M * (Xᵀ * (⅟Ω * (X * M))) = M := by
          have hinner : Xᵀ * (⅟Ω * (X * M)) = (1 : Matrix k k ℝ) := by
            calc
              Xᵀ * (⅟Ω * (X * M)) = (Xᵀ * ⅟Ω * X) * M := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc]
              _ = 1 := by
                simpa [M] using (mul_invOf_self (Xᵀ * ⅟Ω * X))
          rw [hinner]
          simp
        rw [hAXM, hMXM]
      _ = Aᵀ * Ω * A - M := by abel_nf
  have hΩinv : (⅟Ω).PosSemidef := by
    simpa using (Matrix.PosSemidef.inv hΩ)
  have hpsd : (C * ⅟Ω * Cᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose, Matrix.transpose_transpose, Matrix.mul_assoc] using
      (Matrix.PosSemidef.mul_mul_conjTranspose_same hΩinv C)
  exact hgap ▸ hpsd

end HansenEconometrics
