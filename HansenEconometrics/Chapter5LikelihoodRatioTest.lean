import HansenEconometrics.ChiSquared
import HansenEconometrics.FDist
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.ProbabilityUtils
import HansenEconometrics.StudentT
import HansenEconometrics.Chapter3Projections
import HansenEconometrics.Chapter3FWL
import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.Chapter5NormalRegression

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology MeasureTheory ProbabilityTheory

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

section LikelihoodRatioTest

variable {k₁ k₂ : Type*}
variable [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]

/-- The projection increment `P - P₁` that appears in Hansen's likelihood-ratio / F-test
decomposition. It extracts the fitted-value contribution of the second regressor block `X₂` after
controlling for `X₁`. -/
noncomputable def fTestProjectionMatrix
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    Matrix n n ℝ :=
  hatMatrix (Matrix.fromCols X₁ X₂) - hatMatrix X₁

/-- The chi-square numerator in Hansen's F statistic, scaled by the true variance `σ²`. -/
noncomputable def scaledOlsFNumeratorStatistic
    {Ω : Type*}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) (σ2 : ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (ε : Ω → EuclideanSpace ℝ n) : Ω → ℝ :=
  fun ω =>
    (olsResidualSumSquares X₁ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)) -
      olsResidualSumSquares (Matrix.fromCols X₁ X₂) (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))) / σ2

/-- Hansen's F statistic for testing that the right block `β₂` in the partitioned regression
`[X₁ X₂]` is zero. -/
noncomputable def olsFStatistic
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] : ℝ :=
  ((olsResidualSumSquares X₁ y - olsResidualSumSquares (Matrix.fromCols X₁ X₂) y) /
      (Fintype.card k₂ : ℝ)) /
    (olsResidualSumSquares (Matrix.fromCols X₁ X₂) y /
      (Fintype.card n - Fintype.card (Sum k₁ k₂) : ℝ))

lemma fromCols_nullRightBlock_mulVec
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) :
    Matrix.fromCols X₁ X₂ *ᵥ (Sum.elim β₁ (fun _ : k₂ => 0)) = X₁ *ᵥ β₁ := by
  rw [Matrix.fromCols_mulVec]
  change X₁ *ᵥ β₁ + X₂ *ᵥ (0 : k₂ → ℝ) = X₁ *ᵥ β₁
  rw [Matrix.mulVec_zero, add_zero]

theorem hatMatrix_fromCols_mul_left
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    hatMatrix (Matrix.fromCols X₁ X₂) * X₁ = X₁ := by
  have hPX := hat_mul_X (Matrix.fromCols X₁ X₂)
  ext i j
  simpa using congrFun (congrFun hPX i) (Sum.inl j)

theorem leftBlock_transpose_mul_fullAnnihilator
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    X₁ᵀ * annihilatorMatrix (Matrix.fromCols X₁ X₂) = 0 := by
  have h := regressors_transpose_mul_annihilator (Matrix.fromCols X₁ X₂)
  ext i j
  simpa using congrFun (congrFun h (Sum.inl i)) j

theorem fullHat_mul_leftHat
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    hatMatrix (Matrix.fromCols X₁ X₂) * hatMatrix X₁ = hatMatrix X₁ := by
  calc
    hatMatrix (Matrix.fromCols X₁ X₂) * hatMatrix X₁
        = hatMatrix (Matrix.fromCols X₁ X₂) * (X₁ * ⅟ (X₁ᵀ * X₁) * X₁ᵀ) := by
            rfl
    _ = (hatMatrix (Matrix.fromCols X₁ X₂) * (X₁ * ⅟ (X₁ᵀ * X₁))) * X₁ᵀ := by
          rw [← Matrix.mul_assoc]
    _ = ((hatMatrix (Matrix.fromCols X₁ X₂) * X₁) * ⅟ (X₁ᵀ * X₁)) * X₁ᵀ := by
          rw [← Matrix.mul_assoc]
    _ = X₁ * ⅟ (X₁ᵀ * X₁) * X₁ᵀ := by
          rw [hatMatrix_fromCols_mul_left]
    _ = hatMatrix X₁ := by
          rfl

theorem leftHat_mul_fullHat
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    hatMatrix X₁ * hatMatrix (Matrix.fromCols X₁ X₂) = hatMatrix X₁ := by
  have hT := congrArg Matrix.transpose (fullHat_mul_leftHat X₁ X₂)
  simpa [Matrix.transpose_mul, hatMatrix_transpose] using hT

theorem fTestProjectionMatrix_transpose
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (fTestProjectionMatrix X₁ X₂)ᵀ = fTestProjectionMatrix X₁ X₂ := by
  simp [fTestProjectionMatrix, Matrix.transpose_sub, hatMatrix_transpose]

theorem fTestProjectionMatrix_isHermitian
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (fTestProjectionMatrix X₁ X₂).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial _).trans
    (fTestProjectionMatrix_transpose X₁ X₂)

theorem fTestProjectionMatrix_idempotent
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    fTestProjectionMatrix X₁ X₂ * fTestProjectionMatrix X₁ X₂ = fTestProjectionMatrix X₁ X₂ := by
  simp [fTestProjectionMatrix, Matrix.sub_mul, Matrix.mul_sub, fullHat_mul_leftHat,
    leftHat_mul_fullHat, hatMatrix_idempotent]

theorem rank_fTestProjectionMatrix
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (fTestProjectionMatrix X₁ X₂).rank = Fintype.card k₂ := by
  have h :=
    rank_eq_natCast_trace_of_isHermitian_idempotent
      (fTestProjectionMatrix_isHermitian X₁ X₂)
      (fTestProjectionMatrix_idempotent X₁ X₂)
  rw [fTestProjectionMatrix, Matrix.trace_sub, hatMatrix_trace, hatMatrix_trace,
    Fintype.card_sum, Nat.cast_add] at h
  have h' : ((fTestProjectionMatrix X₁ X₂).rank : ℝ) = Fintype.card k₂ := by
    calc
      ((fTestProjectionMatrix X₁ X₂).rank : ℝ)
          = (Fintype.card k₁ : ℝ) + Fintype.card k₂ - Fintype.card k₁ := h
      _ = Fintype.card k₂ := by ring
  exact_mod_cast h'

theorem fTestProjectionMatrix_mul_fullAnnihilator
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    fTestProjectionMatrix X₁ X₂ * annihilatorMatrix (Matrix.fromCols X₁ X₂) = 0 := by
  have hP1M : hatMatrix X₁ * annihilatorMatrix (Matrix.fromCols X₁ X₂) = 0 := by
    unfold hatMatrix
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    rw [leftBlock_transpose_mul_fullAnnihilator X₁ X₂]
    simp
  calc
    fTestProjectionMatrix X₁ X₂ * annihilatorMatrix (Matrix.fromCols X₁ X₂)
        = hatMatrix (Matrix.fromCols X₁ X₂) * annihilatorMatrix (Matrix.fromCols X₁ X₂) -
            hatMatrix X₁ * annihilatorMatrix (Matrix.fromCols X₁ X₂) := by
              simp [fTestProjectionMatrix, Matrix.sub_mul]
    _ = 0 := by
          simp [hatMatrix_mul_annihilator, hP1M]

/-- Generic spectral rewrite for quadratic forms of symmetric idempotent matrices: the quadratic
form is a sum of squared eigenbasis coordinates over the `1`-eigenspace. -/
theorem quadForm_eq_sum_sq_eigCoords_of_isHermitian_idempotent
    (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (hI : IsIdempotentElem A) (e : n → ℝ) :
    let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hA.eigenvectorBasis
    e ⬝ᵥ A *ᵥ e = ∑ i : {j : n // hA.eigenvalues j = 1}, (b.repr (WithLp.toLp 2 e) i.1)^2 := by
  classical
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hA.eigenvectorBasis
  let z : EuclideanSpace ℝ n := WithLp.toLp 2 e
  have hAt : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hcoord : ∀ i : n, b.repr (Matrix.toEuclideanLin A z) i = hA.eigenvalues i * b.repr z i := by
    intro i
    let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin A
    have hSymm : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
    have hEig : T (b i) = hA.eigenvalues i • b i := by
      simpa [T] using congrArg (WithLp.toLp 2) (hA.mulVec_eigenvectorBasis i)
    calc
      b.repr (T z) i = inner ℝ (b i) (T z) := by
        simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := T z) (i := i))
      _ = inner ℝ (T (b i)) z := by rw [← hSymm (b i) z]
      _ = inner ℝ (hA.eigenvalues i • b i) z := by rw [hEig]
      _ = hA.eigenvalues i * b.repr z i := by
        rw [real_inner_smul_left, OrthonormalBasis.repr_apply_apply]
  have hnorm :
      e ⬝ᵥ A *ᵥ e = ∑ i : n, (hA.eigenvalues i * b.repr z i) ^ 2 := by
    let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin A
    calc
      e ⬝ᵥ A *ᵥ e = dotProduct (A *ᵥ e) (A *ᵥ e) := by
        exact quadratic_form_eq_dotProduct_of_symm_idempotent A hAt hI e
      _ = ‖T z‖ ^ 2 := by
        change dotProduct (A *ᵥ e) (A *ᵥ e) = ‖WithLp.toLp 2 (A *ᵥ e)‖ ^ 2
        simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (A *ᵥ e))).symm
      _ = ∑ i : n, ‖inner ℝ (b i) (T z)‖ ^ 2 := by
        symm
        exact OrthonormalBasis.sum_sq_norm_inner_right b (T z)
      _ = ∑ i : n, (b.repr (T z) i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [OrthonormalBasis.repr_apply_apply]
        simp [sq_abs]
      _ = ∑ i : n, (hA.eigenvalues i * b.repr z i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hcoord i]
  have heig01 := eigenvalues_zero_or_one_of_isHermitian_idempotent hA hI
  have hsum :
      ∑ i : n, (hA.eigenvalues i * b.repr z i) ^ 2
        = ∑ i : {j : n // hA.eigenvalues j = 1}, (b.repr z i.1) ^ 2 := by
    calc
      ∑ i : n, (hA.eigenvalues i * b.repr z i) ^ 2
          = ∑ i : n, if hA.eigenvalues i = 1 then (b.repr z i) ^ 2 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases h1 : hA.eigenvalues i = 1
              · simp [h1]
              · have h0 : hA.eigenvalues i = 0 := (heig01 i).resolve_right h1
                simp [h0]
      _ = ∑ i : n with hA.eigenvalues i = 1, (b.repr z i) ^ 2 := by
            rw [Finset.sum_filter]
      _ = ∑ i : {j : n // hA.eigenvalues j = 1}, (b.repr z i.1) ^ 2 := by
            rw [Finset.sum_subtype]
            intro x
            simp
  simpa [b, z] using hnorm.trans hsum

/-- The chi-square numerator in Hansen's F statistic is the squared norm of the projection
increment `P - P₁`, divided by `σ²`. -/
theorem scaledOlsFNumeratorStatistic_eq_projection_norm_sq_div
    {Ω : Type*} [MeasurableSpace Ω]
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) (σ2 : ℝ)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε =
      fun ω =>
        dotProduct
          (fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω))
          (fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω)) / σ2 := by
  classical
  let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
  let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
  let D : Matrix n n ℝ := fTestProjectionMatrix X₁ X₂
  have hβfull : fullX *ᵥ βfull = X₁ *ᵥ β₁ := by
    simpa [fullX, βfull] using fromCols_nullRightBlock_mulVec X₁ X₂ β₁
  funext ω
  let e : n → ℝ := WithLp.ofLp (ε ω)
  have hrestr :
      olsResidualSumSquares X₁ (X₁ *ᵥ β₁ + e) = e ⬝ᵥ (annihilatorMatrix X₁) *ᵥ e := by
    simpa using olsResidualSumSquares_linear_model_quadratic_form X₁ β₁ e
  have hfull :
      olsResidualSumSquares fullX (X₁ *ᵥ β₁ + e) = e ⬝ᵥ (annihilatorMatrix fullX) *ᵥ e := by
    rw [← hβfull]
    simpa [fullX, βfull] using olsResidualSumSquares_linear_model_quadratic_form fullX βfull e
  have hAnnDiff : annihilatorMatrix X₁ - annihilatorMatrix fullX = D := by
    ext i j
    simp [D, fTestProjectionMatrix, annihilatorMatrix]
    ring
  have hquad :
      dotProduct (D *ᵥ e) (D *ᵥ e) = e ⬝ᵥ D *ᵥ e := by
    exact (quadratic_form_eq_dotProduct_of_symm_idempotent D
      (fTestProjectionMatrix_transpose X₁ X₂)
      (fTestProjectionMatrix_idempotent X₁ X₂) e).symm
  calc
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω
        = ((e ⬝ᵥ (annihilatorMatrix X₁) *ᵥ e) -
            (e ⬝ᵥ (annihilatorMatrix fullX) *ᵥ e)) / σ2 := by
              simp [scaledOlsFNumeratorStatistic, e, hrestr, hfull, fullX]
    _ = (e ⬝ᵥ D *ᵥ e) / σ2 := by
          rw [← dotProduct_sub, ← Matrix.sub_mulVec, hAnnDiff]
    _ = dotProduct (D *ᵥ e) (D *ᵥ e) / σ2 := by
          rw [hquad]

theorem scaledOlsFNumeratorStatistic_eq_sum_sq_eigenvector_coords
    {Ω : Type*} [MeasurableSpace Ω]
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    let D := fTestProjectionMatrix X₁ X₂
    let hD : D.IsHermitian := fTestProjectionMatrix_isHermitian X₁ X₂
    let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hD.eigenvectorBasis
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε =
      sumSquaresRV (restrictedStandardizedCoords b
        (fun i : {j : n // hD.eigenvalues j = 1} => i.1) σ2 ε) := by
  classical
  let D : Matrix n n ℝ := fTestProjectionMatrix X₁ X₂
  let hD : D.IsHermitian := fTestProjectionMatrix_isHermitian X₁ X₂
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hD.eigenvectorBasis
  funext ω
  let e : n → ℝ := WithLp.ofLp (ε ω)
  have hquad :
      e ⬝ᵥ D *ᵥ e = ∑ i : {j : n // hD.eigenvalues j = 1}, (b.repr (ε ω) i.1)^2 := by
    simpa [D, hD, b, e] using
      quadForm_eq_sum_sq_eigCoords_of_isHermitian_idempotent
        D hD (fTestProjectionMatrix_idempotent X₁ X₂) e
  have hscaled :
      scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω = (e ⬝ᵥ D *ᵥ e) / σ2 := by
    rw [congrFun (scaledOlsFNumeratorStatistic_eq_projection_norm_sq_div X₁ X₂ β₁ σ2 ε) ω]
    exact congrArg (fun t : ℝ => t / σ2)
      ((quadratic_form_eq_dotProduct_of_symm_idempotent D
        (fTestProjectionMatrix_transpose X₁ X₂)
        (fTestProjectionMatrix_idempotent X₁ X₂) e).symm)
  calc
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω
        = (e ⬝ᵥ D *ᵥ e) / σ2 := hscaled
    _ = (∑ i : {j : n // hD.eigenvalues j = 1}, (b.repr (ε ω) i.1)^2) / σ2 := by rw [hquad]
    _ = ∑ i : {j : n // hD.eigenvalues j = 1}, ((b.repr (ε ω) i.1) / Real.sqrt σ2)^2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro i hi
          field_simp [Real.sq_sqrt hσ2.le, hσ2.ne']
          rw [Real.sq_sqrt hσ2.le]
    _ = sumSquaresRV
          (restrictedStandardizedCoords b
            (fun i : {j : n // hD.eigenvalues j = 1} => i.1) σ2 ε) ω := by
          simp [sumSquaresRV, restrictedStandardizedCoords, standardizedCoords]

/-- Hansen Theorem 5.13, chi-square numerator component: under the null, the restricted-unrestricted
RSS gap divided by `σ²` has a `χ²(q)` law, where `q` is the number of tested restrictions. -/
theorem scaledOlsFNumeratorStatistic_hasLaw_chiSquared
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k₂)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε) (chiSquared (Fintype.card k₂)) μ := by
  classical
  let hD : (fTestProjectionMatrix X₁ X₂).IsHermitian := fTestProjectionMatrix_isHermitian X₁ X₂
  let W : {j : n // hD.eigenvalues j = 1} → Ω → ℝ :=
    restrictedStandardizedCoords hD.eigenvectorBasis
      (fun i : {j : n // hD.eigenvalues j = 1} => i.1) σ2 ε
  have hRankEqCard :
      (fTestProjectionMatrix X₁ X₂).rank = Fintype.card {j : n // hD.eigenvalues j = 1} := by
    simpa [hD] using rank_eq_card_eigenvalues_eq_one_of_isHermitian_idempotent hD
      (fTestProjectionMatrix_idempotent X₁ X₂)
  have hCardPos : 0 < Fintype.card {j : n // hD.eigenvalues j = 1} := by
    rw [← hRankEqCard, rank_fTestProjectionMatrix X₁ X₂]
    exact hq
  have hcoords := orthonormalBasis_coords_div_sqrt_iIndep_standardGaussian
    (b := hD.eigenvectorBasis) hσ2 ε hε
  have hLawW : ∀ i, HasLaw (W i) (gaussianReal 0 1) μ := by
    intro i
    simpa [W, restrictedStandardizedCoords, standardizedCoords] using hcoords.1 i.1
  have hIndepW : ProbabilityTheory.iIndepFun W μ := by
    simpa [W, restrictedStandardizedCoords, standardizedCoords] using
      hcoords.2.precomp Subtype.val_injective
  letI : MeasureSpace Ω := ⟨μ⟩
  have hLawSumSq : HasLaw (sumSquaresRV W)
      (chiSquared (Fintype.card {j : n // hD.eigenvalues j = 1})) μ := by
    simpa [W, sumSquaresRV] using hasLaw_sum_sq_chiSquared_fintype hCardPos hLawW hIndepW
  have hEq := scaledOlsFNumeratorStatistic_eq_sum_sq_eigenvector_coords X₁ X₂ β₁ hσ2 ε
  convert hLawSumSq.congr ?_ using 1
  · rw [← hRankEqCard, rank_fTestProjectionMatrix X₁ X₂]
  · simp [W]

set_option maxHeartbeats 800000 in
-- The independence proof expands large Gaussian covariance and projection identities.
theorem scaledOlsFNumStat_indep_scaledOlsResVarStat
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ⟂ᵢ[μ]
      scaledOlsResidualVarianceStatistic
        (Matrix.fromCols X₁ X₂) (Sum.elim β₁ (fun _ : k₂ => 0)) σ2 ε := by
  classical
  let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
  let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
  let D : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    (Matrix.toEuclideanLin (fTestProjectionMatrix X₁ X₂)).toContinuousLinearMap
  let M : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    (Matrix.toEuclideanLin (annihilatorMatrix fullX)).toContinuousLinearMap
  let numeratorE : Ω → EuclideanSpace ℝ n := fun ω => D (ε ω)
  let residualE : Ω → EuclideanSpace ℝ n := fun ω => M (ε ω)
  have hε_gauss : HasGaussianLaw ε μ := hε.hasGaussianLaw
  have hJoint : HasGaussianLaw (fun ω => (numeratorE ω, residualE ω)) μ := by
    simpa [numeratorE, residualE, D, M] using hε_gauss.map_fun (D.prod M)
  have hCov :
      ∀ x y,
        cov[fun ω => inner ℝ x (numeratorE ω),
          fun ω => inner ℝ y (residualE ω); μ] = 0 := by
    intro x y
    have hDadjointLin :
        (Matrix.toEuclideanLin (fTestProjectionMatrix X₁ X₂)).adjoint =
          Matrix.toEuclideanLin (fTestProjectionMatrix X₁ X₂) := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, fTestProjectionMatrix_transpose] using
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint
          (A := fTestProjectionMatrix X₁ X₂)).symm
    have hMadjointLin :
        (Matrix.toEuclideanLin (annihilatorMatrix fullX)).adjoint =
          Matrix.toEuclideanLin (annihilatorMatrix fullX) := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, annihilatorMatrix_transpose] using
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := annihilatorMatrix fullX)).symm
    have hDadjoint : D.adjoint = D := by
      simpa [D, LinearMap.adjoint_toContinuousLinearMap] using
        congrArg LinearMap.toContinuousLinearMap hDadjointLin
    have hMadjoint : M.adjoint = M := by
      simpa [M, LinearMap.adjoint_toContinuousLinearMap] using
        congrArg LinearMap.toContinuousLinearMap hMadjointLin
    have hcomp : D ∘L M = 0 := by
      ext z i
      simpa [D, M, Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec_mulVec] using
        congrArg (fun A : Matrix n n ℝ => (A *ᵥ (WithLp.ofLp z)) i)
          (fTestProjectionMatrix_mul_fullAnnihilator X₁ X₂)
    have hcomp_apply : D (M y) = 0 := by
      simpa using congrArg (fun T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n => T y) hcomp
    have hcov :=
      hε.covariance_fun_comp
        (f := fun z : EuclideanSpace ℝ n => inner ℝ x (D z))
        (g := fun z : EuclideanSpace ℝ n => inner ℝ y (M z))
        (by fun_prop) (by fun_prop)
    have hDfun :
        (fun z : EuclideanSpace ℝ n => inner ℝ x (D z)) =
          fun z => inner ℝ (D.adjoint x) z := by
      ext z
      simpa [D] using (D.adjoint_inner_left z x).symm
    have hMfun :
        (fun z : EuclideanSpace ℝ n => inner ℝ y (M z)) =
          fun z => inner ℝ (M y) z := by
      ext z
      simpa [hMadjoint] using (M.adjoint_inner_left z y).symm
    have hmem :
        MemLp id 2 (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) :=
      IsGaussian.memLp_two_id
    calc
      cov[fun ω => inner ℝ x (numeratorE ω),
        fun ω => inner ℝ y (residualE ω); μ]
          = cov[fun z : EuclideanSpace ℝ n => inner ℝ (D.adjoint x) z,
              fun z : EuclideanSpace ℝ n => inner ℝ (M y) z;
                multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))] := by
              simpa [numeratorE, residualE, hDfun, hMfun] using hcov
      _ = covarianceBilin (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ)))
            (D.adjoint x) (M y) := by
              symm
              exact covarianceBilin_apply_eq_cov hmem (D.adjoint x) (M y)
      _ = (D.adjoint x) ⬝ᵥ (((σ2 : ℝ) • (1 : Matrix n n ℝ)) *ᵥ (M y)) := by
              rw [covarianceBilin_multivariateGaussian
                (by
                  simpa [smul_one_eq_diagonal] using
                    (Matrix.PosSemidef.diagonal (n := n) (d := fun _ => σ2) fun _ => hσ2.le))]
      _ = (σ2 : ℝ) * ((D.adjoint x : EuclideanSpace ℝ n) ⬝ᵥ (M y)) := by
              simp [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      _ = 0 := by
              have hinner :
                  inner ℝ (D.adjoint x) (M y) = 0 := by
                calc
                  inner ℝ (D.adjoint x) (M y) = inner ℝ x (D (M y)) := by
                    simpa [D] using D.adjoint_inner_left (M y) x
                  _ = 0 := by simp [hcomp_apply]
              have hdot :
                  ((D.adjoint x : EuclideanSpace ℝ n) ⬝ᵥ (M y)) = 0 := by
                have hdot' :
                    (M y).ofLp ⬝ᵥ star (((D.adjoint x : EuclideanSpace ℝ n)).ofLp) = 0 := by
                  simpa [EuclideanSpace.inner_eq_star_dotProduct] using hinner
                simpa [dotProduct, Pi.star_apply, conj_trivial, mul_comm] using hdot'
              rw [hdot, mul_zero]
  have hIndProj : numeratorE ⟂ᵢ[μ] residualE :=
    hJoint.indepFun_of_covariance_inner hCov
  have hIndFunctions :
      (fun ω => fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω)) ⟂ᵢ[μ]
        (fun ω => annihilatorMatrix fullX *ᵥ WithLp.ofLp (ε ω)) := by
    have hIndEuclid :
        (fun ω => WithLp.toLp 2 (fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω))) ⟂ᵢ[μ]
          (fun ω => WithLp.toLp 2 (annihilatorMatrix fullX *ᵥ WithLp.ofLp (ε ω))) := by
      refine (IndepFun.congr hIndProj ?_ ?_)
      · filter_upwards with ω
        simpa [numeratorE, D] using
          (Matrix.toLpLin_apply (p := 2) (q := 2) (fTestProjectionMatrix X₁ X₂) (ε ω))
      · filter_upwards with ω
        simpa [residualE, M] using
          (Matrix.toLpLin_apply (p := 2) (q := 2) (annihilatorMatrix fullX) (ε ω))
    have hmeasN : Measurable (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ) :=
      WithLp.measurable_ofLp (p := 2) (X := n → ℝ)
    simpa using
      (IndepFun.comp (φ := (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ))
        (ψ := (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ))
        hIndEuclid hmeasN hmeasN)
  let q : (n → ℝ) → ℝ := fun r => dotProduct r r / σ2
  have hq : Measurable q := by
    simpa [q] using (Continuous.dotProduct continuous_id continuous_id).div_const σ2 |>.measurable
  have hIndStat :
      (q ∘ fun ω => fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω)) ⟂ᵢ[μ]
        (q ∘ fun ω => annihilatorMatrix fullX *ᵥ WithLp.ofLp (ε ω)) := by
    exact IndepFun.comp (μ := μ) (φ := q) (ψ := q) hIndFunctions hq hq
  refine IndepFun.congr hIndStat ?_ ?_
  · filter_upwards with ω
    simp [Function.comp, q]
    exact (congrFun (scaledOlsFNumeratorStatistic_eq_projection_norm_sq_div
      X₁ X₂ β₁ σ2 ε) ω).symm
  · filter_upwards with ω
    rw [scaledOlsResidualVarianceStatistic_eq_residual_norm_sq_div fullX βfull hdf ε]
    simpa [Function.comp, q, fullX, βfull] using
      congrArg (fun r : n → ℝ => dotProduct r r / σ2)
        ((residual_linear_model fullX βfull (WithLp.ofLp (ε ω))).symm)

theorem olsFStatistic_eq_ratio_of_scaled_chiSquared_statistics
    {Ω : Type*} [MeasurableSpace Ω]
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
    let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
    (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))) =
      fun ω =>
        ((scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω) / (Fintype.card k₂ : ℝ)) /
          (scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω /
            (Fintype.card n - Fintype.card (Sum k₁ k₂) : ℝ)) := by
  classical
  let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
  let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
  have hβfull : fullX *ᵥ βfull = X₁ *ᵥ β₁ := fromCols_nullRightBlock_mulVec X₁ X₂ β₁
  let ν : ℝ := (Fintype.card n - Fintype.card (Sum k₁ k₂) : ℝ)
  have hν_ne : ν ≠ 0 := by
    dsimp [ν]
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hdf))
  ext ω
  let e : n → ℝ := WithLp.ofLp (ε ω)
  let rssR : ℝ := olsResidualSumSquares X₁ (X₁ *ᵥ β₁ + e)
  let rssU : ℝ := olsResidualSumSquares fullX (X₁ *ᵥ β₁ + e)
  have hNum :
      scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω = (rssR - rssU) / σ2 := by
    simp [scaledOlsFNumeratorStatistic, rssR, rssU, e, fullX]
  have hDen :
      scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω = rssU / σ2 := by
    have hν_cast : ((Fintype.card n - Fintype.card (Sum k₁ k₂) : ℕ) : ℝ) = ν := by
      rw [Nat.cast_sub hdf.le]
    calc
      scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω
          = (ν * olsResidualVarianceEstimator fullX (fullX *ᵥ βfull + e)) / σ2 := by
              simp [scaledOlsResidualVarianceStatistic, ν, e]
      _ = (ν * (rssU / ν)) / σ2 := by
            have hrssU : rssU = olsResidualSumSquares fullX (fullX *ᵥ βfull + e) := by
              simp [rssU, hβfull]
            rw [hrssU]
            simp [ν, e, fullX, βfull, olsResidualVarianceEstimator, olsResidualSumSquares]
      _ = rssU / σ2 := by
            field_simp [hν_ne]
  calc
    olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + e)
        = ((rssR - rssU) / (Fintype.card k₂ : ℝ)) / (rssU / ν) := by
            simp [olsFStatistic, rssR, rssU, ν, e, fullX]
    _ = (((rssR - rssU) / σ2) / (Fintype.card k₂ : ℝ)) / ((rssU / σ2) / ν) := by
          field_simp [hσ2.ne']
    _ = ((scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω) / (Fintype.card k₂ : ℝ)) /
          (scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω / ν) := by
            rw [hNum, hDen]

/-- Hansen Theorem 5.13: under the null `β₂ = 0`, the classical block F statistic has the
Fisher-Snedecor law with `q` and `n-k` degrees of freedom. -/
theorem olsFStatistic_hasLaw_fDist
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k₂)
    (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)))
      (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ := by
  -- Proof outline:
  -- 1. Identify the numerator and denominator as independent chi-square statistics.
  -- 2. Rewrite the block F statistic as their normalized ratio.
  -- 3. Apply the generic ratio-of-chi-squares theorem.
  let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
  let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
  have hNum :
      HasLaw (scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε) (chiSquared (Fintype.card k₂)) μ :=
    scaledOlsFNumeratorStatistic_hasLaw_chiSquared X₁ X₂ β₁ hσ2 hq ε hε
  have hDen :
      HasLaw (scaledOlsResidualVarianceStatistic fullX βfull σ2 ε)
        (chiSquared (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ :=
    scaledOlsResidualVarianceStatistic_hasLaw_chiSquared fullX βfull hσ2 hdf ε hε
  have hInd :
      scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ⟂ᵢ[μ]
        scaledOlsResidualVarianceStatistic fullX βfull σ2 ε :=
    scaledOlsFNumStat_indep_scaledOlsResVarStat
      X₁ X₂ β₁ hσ2 hdf ε hε
  have hRatio :
      HasLaw
        (fun ω =>
          ((scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω) / (Fintype.card k₂ : ℝ)) /
            (scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω /
              (Fintype.card n - Fintype.card (Sum k₁ k₂) : ℝ)))
        (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ :=
    by
      have hdf' : Fintype.card k₁ + Fintype.card k₂ ≤ Fintype.card n := by
        exact Nat.le_of_lt (by simpa [Fintype.card_sum] using hdf)
      simpa [Fintype.card_sum, Nat.cast_add, Nat.cast_sub hdf'] using
        (hasLaw_ratio_chiSquared_fDist hq (Nat.sub_pos_of_lt hdf) hNum hDen hInd)
  refine hRatio.congr ?_
  filter_upwards with ω
  simpa [fullX, βfull] using
    congrFun (olsFStatistic_eq_ratio_of_scaled_chiSquared_statistics
      X₁ X₂ β₁ hσ2 hdf ε) ω

/-- Hansen Theorem 5.13 in classical form: the block F statistic has the classical
Fisher-Snedecor distribution under the null. This is a thin wrapper over the ratio-law result
using the standalone `fDist = classicalFDist` bridge in `FDist.lean`. -/
theorem olsFStatistic_hasLaw_classicalFDist
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k₂)
    (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)))
      (classicalFDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ := by
  have hbase :
      HasLaw (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)))
        (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ :=
    olsFStatistic_hasLaw_fDist X₁ X₂ β₁ hσ2 hq hdf ε hε
  rw [fDist_eq_classicalFDist hq (Nat.sub_pos_of_lt hdf)] at hbase
  exact hbase

/-- Hansen Theorem 5.13 rejection statement: if the upper-tail critical value `c` is
calibrated to have F-distribution tail probability `α`, then the rule `F > c` has exact size
`α` under the null. -/
theorem olsFStatistic_rejection_probability_eq_alpha
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 α : ℝ}
    (c : ℝ) (hcrit :
      (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))).real (Set.Ioi c) = α)
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k₂)
    (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} = α := by
  have hF :
      HasLaw (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)))
        (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ :=
    olsFStatistic_hasLaw_fDist X₁ X₂ β₁ hσ2 hq hdf ε hε
  have hPre :
      μ.real {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} =
        (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))).real (Set.Ioi c) := by
    rw [show {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} =
        (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))) ⁻¹' Set.Ioi c by
          ext ω
          simp [Set.mem_Ioi]]
    exact HasLaw.real_preimage_eq hF measurableSet_Ioi
  rw [hPre, hcrit]

/-- Hansen Theorem 5.13 rejection statement in classical form. -/
theorem olsFStatistic_rejection_probability_eq_alpha_classical
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 α : ℝ}
    (c : ℝ) (hcrit :
      (classicalFDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))).real
        (Set.Ioi c) = α)
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k₂)
    (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} = α := by
  have hF :
      HasLaw (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)))
        (classicalFDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ :=
    olsFStatistic_hasLaw_classicalFDist X₁ X₂ β₁ hσ2 hq hdf ε hε
  have hPre :
      μ.real {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} =
        (classicalFDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))).real
          (Set.Ioi c) := by
    rw [show {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} =
        (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))) ⁻¹' Set.Ioi c by
          ext ω
          simp [Set.mem_Ioi]]
    exact HasLaw.real_preimage_eq hF measurableSet_Ioi
  rw [hPre, hcrit]

end LikelihoodRatioTest

end HansenEconometrics
