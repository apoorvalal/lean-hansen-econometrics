import HansenEconometrics.Chapter12InstrumentalVariables.Basic

/-!
# Chapter 12 — LIML notation

This file contains the limited-information maximum-likelihood coefficient
surface used in Hansen's weak- and many-instrument asymptotic theorems.  The
definitions follow the Chapter 12 Star convention: matrix inverses are
totalized through `Matrix.nonsingInv`, so the notation is available without
finite-sample rank side conditions.  The scalar Rayleigh quotient is also
totalized as a function, but its canonical minimizer certificate ranges only
over vectors with strictly positive denominator.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k l : Type*}
variable [Fintype n] [Fintype k] [Fintype l]
variable [DecidableEq n] [DecidableEq k] [DecidableEq l]

/-- LIML weighted projection matrix `P_Z - μ M_Z`, where `M_Z = I - P_Z`.

For `μ = 0` this is the 2SLS projection weight. -/
noncomputable def limlWeightMatrixStar (Z : Matrix n l ℝ) (μhat : ℝ) :
    Matrix n n ℝ :=
  instrumentProjectionStar Z -
    μhat • ((1 : Matrix n n ℝ) - instrumentProjectionStar Z)

/-- LIML sample moment matrix `X'(P_Z - μ M_Z)X`. -/
noncomputable def limlMomentMatrixStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (μhat : ℝ) : Matrix k k ℝ :=
  Xᵀ * limlWeightMatrixStar Z μhat * X

/-- LIML sample cross moment `X'(P_Z - μ M_Z)Y`. -/
noncomputable def limlMomentVectorStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (μhat : ℝ) : k → ℝ :=
  (Xᵀ * limlWeightMatrixStar Z μhat) *ᵥ Y

/-- Star primitive for Hansen's LIML estimator,
`β̂_LIML = (X'(P_Z - μ M_Z)X)^{-1} X'(P_Z - μ M_Z)Y`. -/
noncomputable def limlBetaStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (μhat : ℝ) : k → ℝ :=
  (limlMomentMatrixStar Z X μhat)⁻¹ *ᵥ limlMomentVectorStar Z X Y μhat

/-- Hansen-normalized LIML moment matrix `n^{-1}X'(P_Z - μM_Z)X`. -/
noncomputable def limlNormalizedMomentMatrixStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (μhat : ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • limlMomentMatrixStar Z X μhat

/-- Hansen-normalized LIML moment vector `n^{-1}X'(P_Z - μM_Z)Y`. -/
noncomputable def limlNormalizedMomentVectorStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (μhat : ℝ) : k → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • limlMomentVectorStar Z X Y μhat

omit [Fintype k] [DecidableEq k] in
/-- A normalized LIML bread is its zero-adjustment value minus the adjustment
times the residual OLS bread. -/
theorem limlNormalizedMomentMatrixStar_eq_zero_sub_mu_residual
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (muHat : ℝ) :
    limlNormalizedMomentMatrixStar Z X muHat =
      limlNormalizedMomentMatrixStar Z X 0 -
        muHat • (sampleGram X - limlNormalizedMomentMatrixStar Z X 0) := by
  ext a b
  simp [limlNormalizedMomentMatrixStar, limlMomentMatrixStar, limlWeightMatrixStar,
    sampleGram, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  ring

omit [Fintype k] [DecidableEq k] in
/-- A normalized LIML score is its zero-adjustment value minus the adjustment
times the residual OLS score. -/
theorem limlNormalizedMomentVectorStar_eq_zero_sub_mu_residual
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) (muHat : ℝ) :
    limlNormalizedMomentVectorStar Z X e muHat =
      limlNormalizedMomentVectorStar Z X e 0 -
        muHat • (sampleCrossMoment X e - limlNormalizedMomentVectorStar Z X e 0) := by
  ext a
  simp [limlNormalizedMomentVectorStar, limlMomentVectorStar, limlWeightMatrixStar,
    sampleCrossMoment, Matrix.mul_sub, Matrix.sub_mulVec, Matrix.smul_mulVec]
  ring_nf

omit [DecidableEq k] in
/-- LIML cross moments split under the structural equation `Y = Xβ + e`. -/
theorem limlMomentVectorStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    (μhat : ℝ) :
    limlMomentVectorStar Z X (X *ᵥ β + e) μhat =
      limlMomentMatrixStar Z X μhat *ᵥ β + limlMomentVectorStar Z X e μhat := by
  unfold limlMomentVectorStar limlMomentMatrixStar
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]

omit [DecidableEq k] in
/-- Hansen-normalized LIML cross moments split under the structural equation. -/
theorem limlNormalizedMomentVectorStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    (μhat : ℝ) :
    limlNormalizedMomentVectorStar Z X (X *ᵥ β + e) μhat =
      limlNormalizedMomentMatrixStar Z X μhat *ᵥ β +
        limlNormalizedMomentVectorStar Z X e μhat := by
  unfold limlNormalizedMomentVectorStar limlNormalizedMomentMatrixStar
  rw [limlMomentVectorStar_linear_model]
  simp [Matrix.smul_mulVec]

/-- LIML is unchanged by Hansen's `n^{-1}` normalization of both moments on
nonempty samples. -/
theorem limlBetaStar_eq_normalized_moments
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (μhat : ℝ)
    [Nonempty n] :
    limlBetaStar Z X Y μhat =
      (limlNormalizedMomentMatrixStar Z X μhat)⁻¹ *ᵥ
        limlNormalizedMomentVectorStar Z X Y μhat := by
  have hN : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold limlBetaStar limlNormalizedMomentMatrixStar limlNormalizedMomentVectorStar
  rw [nonsingInv_smul]
  simp [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, hN]

/-- On nonsingular LIML normalized moments, the centered LIML estimator is the
inverse normalized LIML bread times the normalized structural-error score. -/
theorem limlBetaStar_sub_eq_normalizedScore_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    (μhat : ℝ) [Nonempty n]
    (hunit : IsUnit (limlNormalizedMomentMatrixStar Z X μhat).det) :
    limlBetaStar Z X (X *ᵥ β + e) μhat - β =
      (limlNormalizedMomentMatrixStar Z X μhat)⁻¹ *ᵥ
        limlNormalizedMomentVectorStar Z X e μhat := by
  rw [limlBetaStar_eq_normalized_moments,
    limlNormalizedMomentVectorStar_linear_model,
    Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hunit]
  ext i
  simp [Pi.sub_apply, Pi.add_apply]

omit [Fintype n] [DecidableEq n] in
/-- Rayleigh quotient appearing in Hansen's weak-instrument LIML limit:
`γ' A γ / γ' Σ γ`.

Division on `ℝ` is totalized, so the quotient is merely notation at vectors
where `γ'Σγ = 0`.  `LIMLRayleighMinimizer` excludes those vectors from its
optimization domain. -/
noncomputable def limlRayleighQuotient
    (A Sigma : Matrix k k ℝ) (γ : k → ℝ) : ℝ :=
  (γ ⬝ᵥ (A *ᵥ γ)) / (γ ⬝ᵥ (Sigma *ᵥ γ))

omit [Fintype n] [DecidableEq n] in
/-- Admissibility condition for Hansen's generalized Rayleigh quotient:
the denominator `γ'Σγ` is strictly positive. -/
def limlRayleighAdmissible
    (Sigma : Matrix k k ℝ) (γ : k → ℝ) : Prop :=
  0 < γ ⬝ᵥ (Sigma *ᵥ γ)

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- An admissible generalized-Rayleigh vector is nonzero. -/
theorem limlRayleighAdmissible.ne_zero
    {Sigma : Matrix k k ℝ} {γ : k → ℝ}
    (hγ : limlRayleighAdmissible Sigma γ) : γ ≠ 0 := by
  intro hzero
  subst γ
  simp [limlRayleighAdmissible] at hγ

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Positive definiteness makes every nonzero vector Rayleigh-admissible. -/
theorem limlRayleighAdmissible_of_posDef
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.PosDef) {γ : k → ℝ}
    (hγ : γ ≠ 0) : limlRayleighAdmissible Sigma γ := by
  simpa [limlRayleighAdmissible] using hSigma.dotProduct_mulVec_pos hγ

omit [Fintype n] [DecidableEq n] in
/-- Hansen's weak-instrument `µ*` minimizer certificate for the LIML
   Rayleigh quotient.  The scalar `mustar` is the minimum value of
   `γ' A γ / γ'Σγ` over vectors satisfying `γ'Σγ > 0`.  This domain restriction
   prevents totalized division at a zero denominator from creating a spurious
   minimizer. -/
structure LIMLRayleighMinimizer
    (A Sigma : Matrix k k ℝ) (mustar : ℝ) : Prop where
  value : ∃ γ : k → ℝ,
    limlRayleighAdmissible Sigma γ ∧ limlRayleighQuotient A Sigma γ = mustar
  lower_bound : ∀ γ : k → ℝ, limlRayleighAdmissible Sigma γ →
    mustar ≤ limlRayleighQuotient A Sigma γ

omit [Fintype n] [DecidableEq n] in
/-- Compatibility certificate minimizing the totalized Rayleigh quotient over
all nonzero vectors.

This is equivalent to `LIMLRayleighMinimizer` when `Sigma.PosDef`.  Without
that hypothesis it is not Hansen's generalized Rayleigh minimization problem,
because vectors with zero denominator remain in the domain. -/
structure LIMLTotalizedRayleighMinimizer
    (A Sigma : Matrix k k ℝ) (mustar : ℝ) : Prop where
  value : ∃ γ : k → ℝ, γ ≠ 0 ∧ limlRayleighQuotient A Sigma γ = mustar
  lower_bound : ∀ γ : k → ℝ, γ ≠ 0 → mustar ≤ limlRayleighQuotient A Sigma γ

namespace LIMLRayleighMinimizer

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Construct the denominator-safe minimizer from the totalized compatibility
certificate when the denominator matrix is positive definite. -/
theorem of_totalized_of_posDef
    {A Sigma : Matrix k k ℝ} {mustar : ℝ} (hSigma : Sigma.PosDef)
    (hmin : LIMLTotalizedRayleighMinimizer A Sigma mustar) :
    LIMLRayleighMinimizer A Sigma mustar := by
  refine ⟨?_, ?_⟩
  · rcases hmin.value with ⟨γ, hγ, hvalue⟩
    exact ⟨γ, limlRayleighAdmissible_of_posDef hSigma hγ, hvalue⟩
  · intro γ hγ
    exact hmin.lower_bound γ hγ.ne_zero

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Recover the totalized compatibility certificate from the canonical
minimizer when the denominator matrix is positive definite. -/
theorem to_totalized_of_posDef
    {A Sigma : Matrix k k ℝ} {mustar : ℝ}
    (hmin : LIMLRayleighMinimizer A Sigma mustar) (hSigma : Sigma.PosDef) :
    LIMLTotalizedRayleighMinimizer A Sigma mustar := by
  refine ⟨?_, ?_⟩
  · rcases hmin.value with ⟨γ, hγ, hvalue⟩
    exact ⟨γ, hγ.ne_zero, hvalue⟩
  · intro γ hγ
    exact hmin.lower_bound γ (limlRayleighAdmissible_of_posDef hSigma hγ)

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- With a positive-definite denominator matrix, the canonical and totalized
Rayleigh minimizer certificates are equivalent. -/
theorem iff_totalized_of_posDef
    {A Sigma : Matrix k k ℝ} {mustar : ℝ} (hSigma : Sigma.PosDef) :
    LIMLRayleighMinimizer A Sigma mustar ↔
      LIMLTotalizedRayleighMinimizer A Sigma mustar :=
  ⟨fun hmin ↦ hmin.to_totalized_of_posDef hSigma,
    fun hmin ↦ of_totalized_of_posDef hSigma hmin⟩

end LIMLRayleighMinimizer

omit [Fintype n] [DecidableEq n] in
/-- Matrix whose quadratic form gives Hansen's LIML Rayleigh numerator,
`γ' A' Q^{-1} A γ`.  Weak- and many-instrument files instantiate `A` with
their chapter-specific Gaussian first-stage limits. -/
noncomputable def limlRayleighMatrix
    (Q : Matrix l l ℝ) (A : Matrix l k ℝ) : Matrix k k ℝ :=
  Aᵀ * Q⁻¹ * A

/-- Hansen's k-class weight matrix `I - κ M_Z`, where `M_Z = I - P_Z`.

The LIML representation in Hansen (12.37) uses `κ`; the asymptotic
representation in Section 12.19 uses `μ = κ - 1`. -/
noncomputable def limlKClassWeightMatrixStar (Z : Matrix n l ℝ) (kappa : ℝ) :
    Matrix n n ℝ :=
  (1 : Matrix n n ℝ) - kappa • ((1 : Matrix n n ℝ) - instrumentProjectionStar Z)

/-- k-class sample moment matrix `X'(I - κM_Z)X`. -/
noncomputable def limlKClassMomentMatrixStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (kappa : ℝ) : Matrix k k ℝ :=
  Xᵀ * limlKClassWeightMatrixStar Z kappa * X

/-- k-class sample cross moment `X'(I - κM_Z)Y`. -/
noncomputable def limlKClassMomentVectorStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (kappa : ℝ) : k → ℝ :=
  (Xᵀ * limlKClassWeightMatrixStar Z kappa) *ᵥ Y

/-- Star primitive for Hansen's k-class estimator.  Special cases:
`κ = 0` gives OLS and `κ = 1` gives 2SLS. -/
noncomputable def limlKClassBetaStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (kappa : ℝ) : k → ℝ :=
  (limlKClassMomentMatrixStar Z X kappa)⁻¹ *ᵥ
    limlKClassMomentVectorStar Z X Y kappa

omit [DecidableEq k] in
/-- K-class cross moments split under the structural equation `Y = Xβ + e`. -/
theorem limlKClassMomentVectorStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    (kappa : ℝ) :
    limlKClassMomentVectorStar Z X (X *ᵥ β + e) kappa =
      limlKClassMomentMatrixStar Z X kappa *ᵥ β +
        limlKClassMomentVectorStar Z X e kappa := by
  unfold limlKClassMomentVectorStar limlKClassMomentMatrixStar
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]

/-- On nonsingular k-class moments, the centered k-class estimator is inverse
k-class bread times the structural-error k-class score. -/
theorem limlKClassBetaStar_sub_eq_score_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    (kappa : ℝ)
    (hunit : IsUnit (limlKClassMomentMatrixStar Z X kappa).det) :
    limlKClassBetaStar Z X (X *ᵥ β + e) kappa - β =
      (limlKClassMomentMatrixStar Z X kappa)⁻¹ *ᵥ
        limlKClassMomentVectorStar Z X e kappa := by
  unfold limlKClassBetaStar
  rw [limlKClassMomentVectorStar_linear_model,
    Matrix.mulVec_add, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hunit]
  ext i
  simp [Pi.sub_apply, Pi.add_apply]

@[simp]
theorem limlWeightMatrixStar_zero (Z : Matrix n l ℝ) :
    limlWeightMatrixStar Z 0 = instrumentProjectionStar Z := by
  simp [limlWeightMatrixStar]

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem limlMomentMatrixStar_zero (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    limlMomentMatrixStar Z X 0 = twoSLSMomentMatrixStar Z X := by
  simp [limlMomentMatrixStar, twoSLSMomentMatrixStar]

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem limlMomentVectorStar_zero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    limlMomentVectorStar Z X Y 0 = twoSLSMomentVectorStar Z X Y := by
  simp [limlMomentVectorStar, twoSLSMomentVectorStar]

@[simp]
theorem limlBetaStar_zero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    limlBetaStar Z X Y 0 = twoSLSBetaStar Z X Y := by
  simp [limlBetaStar, twoSLSBetaStar]

/-- The Section 12.19 `μ` parametrization is the k-class parametrization with
`κ = μ + 1`. -/
theorem limlWeightMatrixStar_eq_kClass_add_one (Z : Matrix n l ℝ) (μhat : ℝ) :
    limlWeightMatrixStar Z μhat =
      limlKClassWeightMatrixStar Z (μhat + 1) := by
  ext i j
  simp [limlWeightMatrixStar, limlKClassWeightMatrixStar]
  ring

/-- Conversely, Hansen's k-class parameter `κ` corresponds to
`μ = κ - 1` in the LIML asymptotic representation. -/
theorem limlKClassWeightMatrixStar_eq_liml_sub_one
    (Z : Matrix n l ℝ) (kappa : ℝ) :
    limlKClassWeightMatrixStar Z kappa =
      limlWeightMatrixStar Z (kappa - 1) := by
  rw [limlWeightMatrixStar_eq_kClass_add_one]
  ring_nf

@[simp]
theorem limlKClassWeightMatrixStar_zero (Z : Matrix n l ℝ) :
    limlKClassWeightMatrixStar Z 0 = 1 := by
  simp [limlKClassWeightMatrixStar]

@[simp]
theorem limlKClassWeightMatrixStar_one (Z : Matrix n l ℝ) :
    limlKClassWeightMatrixStar Z 1 = instrumentProjectionStar Z := by
  ext i j
  simp [limlKClassWeightMatrixStar]

/-- In Hansen's `μ = κ - 1` parametrization, `μ = -1` is OLS. -/
@[simp]
theorem limlWeightMatrixStar_neg_one (Z : Matrix n l ℝ) :
    limlWeightMatrixStar Z (-1) = 1 := by
  rw [limlWeightMatrixStar_eq_kClass_add_one]
  norm_num

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem limlMomentMatrixStar_neg_one (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    limlMomentMatrixStar Z X (-1) = Xᵀ * X := by
  simp [limlMomentMatrixStar]

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem limlMomentVectorStar_neg_one
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    limlMomentVectorStar Z X Y (-1) = Xᵀ *ᵥ Y := by
  simp [limlMomentVectorStar]

omit [Fintype k] [DecidableEq k] in
theorem limlMomentMatrixStar_eq_kClass_add_one
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (μhat : ℝ) :
    limlMomentMatrixStar Z X μhat =
      limlKClassMomentMatrixStar Z X (μhat + 1) := by
  simp [limlMomentMatrixStar, limlKClassMomentMatrixStar,
    limlWeightMatrixStar_eq_kClass_add_one]

omit [Fintype k] [DecidableEq k] in
theorem limlMomentVectorStar_eq_kClass_add_one
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (μhat : ℝ) :
    limlMomentVectorStar Z X Y μhat =
      limlKClassMomentVectorStar Z X Y (μhat + 1) := by
  simp [limlMomentVectorStar, limlKClassMomentVectorStar,
    limlWeightMatrixStar_eq_kClass_add_one]

/-- LIML with asymptotic adjustment `μ` is the k-class estimator with
`κ = μ + 1`. -/
theorem limlBetaStar_eq_kClass_add_one
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) (μhat : ℝ) :
    limlBetaStar Z X Y μhat =
      limlKClassBetaStar Z X Y (μhat + 1) := by
  simp [limlBetaStar, limlKClassBetaStar,
    limlMomentMatrixStar_eq_kClass_add_one,
    limlMomentVectorStar_eq_kClass_add_one]

/-- The k-class estimator with `κ = 0` is OLS. -/
@[simp]
theorem limlKClassBetaStar_zero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    limlKClassBetaStar Z X Y 0 = olsBetaStar X Y := by
  simp [limlKClassBetaStar, limlKClassMomentMatrixStar,
    limlKClassMomentVectorStar, olsBetaStar]

/-- The k-class estimator with `κ = 1` is 2SLS. -/
@[simp]
theorem limlKClassBetaStar_one
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    limlKClassBetaStar Z X Y 1 = twoSLSBetaStar Z X Y := by
  simp [limlKClassBetaStar, limlKClassMomentMatrixStar,
    limlKClassMomentVectorStar, twoSLSBetaStar, twoSLSMomentMatrixStar,
    twoSLSMomentVectorStar]

/-- In Hansen's `μ = κ - 1` parametrization, `μ = -1` gives OLS. -/
@[simp]
theorem limlBetaStar_neg_one
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    limlBetaStar Z X Y (-1) = olsBetaStar X Y := by
  simp [limlBetaStar, olsBetaStar]

end HansenEconometrics
