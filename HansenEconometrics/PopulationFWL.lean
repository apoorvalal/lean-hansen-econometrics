import HansenEconometrics.Chapter2LinearProjection
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Population partial regression

Partial regression in a real inner product space with a projected control subspace.
Specializing the space to `Lp ℝ 2 μ` gives population least squares. The coefficient
is built from residual Gram moments, and its least-squares characterization is
proved rather than assumed. Control projections use Mathlib's existing API.
-/

open scoped Matrix

namespace HansenEconometrics.PopulationFWL

variable {E k : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype k] [DecidableEq k]

/-- Linear predictor formed from finitely many regressors. -/
def predictor (X : k → E) (b : k → ℝ) : E := ∑ j, b j • X j

/-- Regressors after projecting out the control subspace. -/
noncomputable def residualized (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) : k → E := fun j => X j - G.starProjection (X j)

/-- The partial-regression coefficient obtained from residual Gram moments. -/
noncomputable def coefficient (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) [Invertible (Matrix.gram ℝ (residualized G X))] : k → ℝ :=
  linearProjectionBeta (Matrix.gram ℝ (residualized G X))
    (fun j => inner ℝ (residualized G X j) Y)

/-- Optimal control fit for a specified treatment coefficient. -/
noncomputable def controlFit (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) (b : k → ℝ) : E :=
  G.starProjection (Y - predictor X b)

/-- Residual of the joint treatment and control fit. -/
noncomputable def error (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) [Invertible (Matrix.gram ℝ (residualized G X))] : E :=
  Y - predictor X (coefficient G X Y) - controlFit G X Y (coefficient G X Y)

omit [DecidableEq k] in
@[simp] theorem controlFit_mem (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) (b : k → ℝ) : controlFit G X Y b ∈ G :=
  G.starProjection_apply_mem _

omit [DecidableEq k] in
private theorem inner_predictor (X : k → E) (b : k → ℝ) (v : E) :
    inner ℝ v (predictor X b) = ∑ j, b j * inner ℝ v (X j) := by
  simp [predictor, inner_sum, inner_smul_right]

omit [Fintype k] [DecidableEq k] in
/-- Control-residualized regressors are orthogonal to every included control. -/
theorem residualized_inner_control (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (j : k) {g : E} (hg : g ∈ G) :
    inner ℝ (residualized G X j) g = 0 :=
  G.starProjection_inner_eq_zero _ g hg

omit [Fintype k] [DecidableEq k] in
private theorem residualized_inner_regressor (G : Submodule ℝ E)
    [G.HasOrthogonalProjection] (X : k → E) (i j : k) :
    inner ℝ (residualized G X i) (X j) =
      inner ℝ (residualized G X i) (residualized G X j) := by
  change inner ℝ (residualized G X i) (X j) =
    inner ℝ (residualized G X i) (X j - G.starProjection (X j))
  rw [inner_sub_right,
    residualized_inner_control G X i (G.starProjection_apply_mem _), sub_zero]

/-- The joint least-squares error is orthogonal to the control subspace. -/
theorem error_inner_control (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) [Invertible (Matrix.gram ℝ (residualized G X))]
    {g : E} (hg : g ∈ G) : inner ℝ (error G X Y) g = 0 :=
  G.starProjection_inner_eq_zero _ g hg

/-- The residual Gram normal equations imply orthogonality to each residualized regressor. -/
theorem residualized_inner_error (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    inner ℝ (residualized G X j) (error G X Y) = 0 := by
  have hn := congrFun (linearProjectionBeta_normal_equations
    (Matrix.gram ℝ (residualized G X)) (fun i => inner ℝ (residualized G X i) Y)) j
  change (Matrix.gram ℝ (residualized G X) *ᵥ coefficient G X Y) j = _ at hn
  simp only [Matrix.mulVec, dotProduct, Matrix.gram_apply] at hn
  rw [error, inner_sub_right, inner_sub_right, inner_predictor,
    residualized_inner_control G X j (controlFit_mem G X Y _)]
  simp_rw [residualized_inner_regressor G X, mul_comm (coefficient G X Y _)]
  linarith

/-- The joint error is orthogonal to the original treatment regressors. -/
theorem error_inner_regressor (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    inner ℝ (error G X Y) (X j) = 0 := by
  have hr := residualized_inner_error G X Y j
  rw [real_inner_comm] at hr
  change inner ℝ (error G X Y) (X j - G.starProjection (X j)) = 0 at hr
  rw [inner_sub_right, error_inner_control G X Y (G.starProjection_apply_mem _),
    sub_zero] at hr
  exact hr

/-- Residual normal equations uniquely identify the treatment coefficient,
independently of the choice of control fit. -/
theorem eq_coefficient_of_normal_equations (G : Submodule ℝ E)
    [G.HasOrthogonalProjection] (X : k → E) (Y : E)
    [Invertible (Matrix.gram ℝ (residualized G X))]
    (b : k → ℝ) {g : E} (hg : g ∈ G)
    (hb : ∀ j, inner ℝ (residualized G X j) (Y - predictor X b - g) = 0) :
    b = coefficient G X Y := by
  symm
  apply linearProjectionBeta_eq_of_normal_equations
  funext j
  have h := hb j
  rw [inner_sub_right, inner_sub_right, inner_predictor,
    residualized_inner_control G X j hg] at h
  simp_rw [residualized_inner_regressor G X] at h
  change ∑ i, inner ℝ (residualized G X j) (residualized G X i) * b i = _
  simp_rw [mul_comm _ (b _)]
  linarith

/-- Pythagorean decomposition of the joint least-squares criterion around its fit. -/
theorem loss_eq_optimum_add_sq (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) [Invertible (Matrix.gram ℝ (residualized G X))]
    (b : k → ℝ) {g : E} (hg : g ∈ G) :
    ‖Y - predictor X b - g‖ ^ 2 = ‖error G X Y‖ ^ 2 +
      ‖predictor X (coefficient G X Y) + controlFit G X Y (coefficient G X Y) -
        predictor X b - g‖ ^ 2 := by
  let d := predictor X (coefficient G X Y) + controlFit G X Y (coefficient G X Y) -
    predictor X b - g
  have hd : inner ℝ (error G X Y) d = 0 := by
    dsimp [d]
    simp only [inner_sub_right, inner_add_right, inner_predictor,
      error_inner_regressor, mul_zero, Finset.sum_const_zero,
      error_inner_control G X Y (controlFit_mem G X Y _),
      error_inner_control G X Y hg, add_zero, sub_zero]
  have heq : Y - predictor X b - g = error G X Y + d := by
    dsimp [error, d]
    abel
  change ‖Y - predictor X b - g‖ ^ 2 = ‖error G X Y‖ ^ 2 + ‖d‖ ^ 2
  rw [heq, norm_add_sq_real, hd]
  ring

/-- Population FWL: the residual-moment coefficient and its control fit jointly
minimize squared prediction error over all treatment coefficients and controls. -/
theorem minimizes (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) [Invertible (Matrix.gram ℝ (residualized G X))]
    (b : k → ℝ) {g : E} (hg : g ∈ G) :
    ‖error G X Y‖ ^ 2 ≤ ‖Y - predictor X b - g‖ ^ 2 := by
  rw [loss_eq_optimum_add_sq G X Y b hg]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Any minimizing joint fit has the partial-regression treatment coefficient.
Controls need only be unique as elements of the inner product space. -/
theorem coefficient_unique (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) (Y : E) [Invertible (Matrix.gram ℝ (residualized G X))]
    (b : k → ℝ) {g : E} (hg : g ∈ G)
    (hmin : ‖Y - predictor X b - g‖ ^ 2 ≤ ‖error G X Y‖ ^ 2) :
    b = coefficient G X Y := by
  have hl := loss_eq_optimum_add_sq G X Y b hg
  have hd : predictor X (coefficient G X Y) + controlFit G X Y (coefficient G X Y) -
      predictor X b - g = 0 := by
    have hz : ‖predictor X (coefficient G X Y) +
        controlFit G X Y (coefficient G X Y) - predictor X b - g‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖predictor X (coefficient G X Y) +
        controlFit G X Y (coefficient G X Y) - predictor X b - g‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have he : Y - predictor X b - g = error G X Y := by
    calc
      Y - predictor X b - g = error G X Y +
          (predictor X (coefficient G X Y) + controlFit G X Y (coefficient G X Y) -
            predictor X b - g) := by unfold error; abel
      _ = error G X Y := by rw [hd, add_zero]
  apply eq_coefficient_of_normal_equations G X Y b hg
  intro j
  rw [he]
  exact residualized_inner_error G X Y j

/-- Dual residual regressor: its inner product extracts a treatment coefficient. -/
noncomputable def dualRegressor (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) : E :=
  predictor (residualized G X) (fun i => (⅟ (Matrix.gram ℝ (residualized G X))) j i)

/-- Dual residual regressors are orthogonal to the controls. -/
theorem dualRegressor_inner_control (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k)
    {g : E} (hg : g ∈ G) : inner ℝ (dualRegressor G X j) g = 0 := by
  simp [dualRegressor, predictor, sum_inner, real_inner_smul_left,
    residualized_inner_control G X _ hg]

/-- The dual residual Gram moments are the entries of the identity matrix. -/
theorem dualRegressor_inner_residualized (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j l : k) :
    inner ℝ (dualRegressor G X j) (residualized G X l) = if j = l then 1 else 0 := by
  have h := congrArg (fun A : Matrix k k ℝ => A j l)
    (invOf_mul_self (Matrix.gram ℝ (residualized G X)))
  simpa [dualRegressor, predictor, sum_inner, real_inner_smul_left,
    Matrix.mul_apply, Matrix.gram_apply, Matrix.one_apply] using h

/-- The dual regressor has unit moment with its own treatment and zero moments with the others. -/
theorem dualRegressor_inner_regressor (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j l : k) :
    inner ℝ (dualRegressor G X j) (X l) = if j = l then 1 else 0 := by
  have h := dualRegressor_inner_residualized G X j l
  change inner ℝ (dualRegressor G X j) (X l - G.starProjection (X l)) = _ at h
  rwa [inner_sub_right, dualRegressor_inner_control G X j
    (G.starProjection_apply_mem _), sub_zero] at h

/-- The inner product against the dual regressor is the actual regression coefficient. -/
theorem coefficient_eq_inner_dualRegressor (G : Submodule ℝ E)
    [G.HasOrthogonalProjection] (X : k → E) (Y : E)
    [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    coefficient G X Y j = inner ℝ (dualRegressor G X j) Y := by
  simp [coefficient, linearProjectionBeta, Matrix.mulVec, dotProduct,
    dualRegressor, predictor, sum_inner, real_inner_smul_left]

/-- Identification makes the dual residual nonzero. -/
theorem dualRegressor_ne_zero (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    dualRegressor G X j ≠ 0 := by
  intro h
  have hi := dualRegressor_inner_regressor G X j j
  simp [h] at hi

/-- The diagonal inverse Gram entry is the squared norm of the dual residual. -/
theorem inverse_gram_diag_eq_norm_sq (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    (⅟ (Matrix.gram ℝ (residualized G X))) j j = ‖dualRegressor G X j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  conv_rhs => rhs; unfold dualRegressor
  rw [inner_predictor]
  simp [dualRegressor_inner_residualized]

/-- Residual of one treatment after partialling out all other treatments and the controls.
Its projection characterization is established below. -/
noncomputable def auxiliaryResidual (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) : E :=
  (‖dualRegressor G X j‖ ^ 2)⁻¹ • dualRegressor G X j

/-- The auxiliary residual has strictly positive variance. -/
theorem auxiliaryResidual_norm_sq_pos (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    0 < ‖auxiliaryResidual G X j‖ ^ 2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  exact smul_ne_zero (inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr
    (dualRegressor_ne_zero G X j)))) (dualRegressor_ne_zero G X j)

/-- Scalar population FWL formula in the auxiliary-residual notation. -/
theorem coefficient_eq_auxiliaryResidual_ratio (G : Submodule ℝ E)
    [G.HasOrthogonalProjection] (X : k → E) (Y : E)
    [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    coefficient G X Y j =
      inner ℝ (auxiliaryResidual G X j) Y / ‖auxiliaryResidual G X j‖ ^ 2 := by
  rw [coefficient_eq_inner_dualRegressor]
  have hn : ‖dualRegressor G X j‖ ≠ 0 := norm_ne_zero_iff.mpr
    (dualRegressor_ne_zero G X j)
  simp only [auxiliaryResidual, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_pow, abs_norm]
  field_simp

/-- The controls and all treatment regressors other than a specified arm. -/
def auxiliaryControls (G : Submodule ℝ E) (X : k → E) (j : k) : Submodule ℝ E :=
  G ⊔ Submodule.span ℝ (X '' {i | i ≠ j})

private theorem dualRegressor_inner_auxiliaryControls (G : Submodule ℝ E)
    [G.HasOrthogonalProjection] (X : k → E)
    [Invertible (Matrix.gram ℝ (residualized G X))] (j : k)
    {g : E} (hg : g ∈ auxiliaryControls G X j) :
    inner ℝ (dualRegressor G X j) g = 0 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hg
  rw [inner_add_right, dualRegressor_inner_control G X j hu, zero_add]
  clear hg
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    simp [dualRegressor_inner_regressor, Ne.symm hi]
  | zero => simp
  | add u v _ _ hu hv => simp [inner_add_right, hu, hv]
  | smul a v _ hv => simp [inner_smul_right, hv]

private theorem regressor_sub_auxiliaryResidual_mem (G : Submodule ℝ E)
    [G.HasOrthogonalProjection] (X : k → E)
    [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    X j - auxiliaryResidual G X j ∈ auxiliaryControls G X j := by
  let a : k → ℝ := fun i => (⅟ (Matrix.gram ℝ (residualized G X))) j i
  have ha : a j ≠ 0 := by
    dsimp [a]
    rw [inverse_gram_diag_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (dualRegressor_ne_zero G X j))
  have hsplit : auxiliaryResidual G X j = residualized G X j +
      ∑ i ∈ Finset.univ.erase j, ((a j)⁻¹ * a i) • residualized G X i := by
    unfold auxiliaryResidual
    rw [← inverse_gram_diag_eq_norm_sq]
    unfold dualRegressor predictor
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp only [smul_add, Finset.smul_sum, smul_smul]
    dsimp [a]
    rw [inv_mul_cancel₀ ha, one_smul, add_comm]
  rw [hsplit, ← sub_sub, show X j - residualized G X j = G.starProjection (X j) by
    unfold residualized; abel]
  apply Submodule.sub_mem
  · exact (show G ≤ auxiliaryControls G X j from le_sup_left) (G.starProjection_apply_mem _)
  · apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · apply (show Submodule.span ℝ (X '' {i | i ≠ j}) ≤ auxiliaryControls G X j from
        le_sup_right)
      apply Submodule.subset_span
      exact ⟨i, (Finset.mem_erase.mp hi).1, rfl⟩
    · exact (show G ≤ auxiliaryControls G X j from le_sup_left) (G.starProjection_apply_mem _)

/-- The auxiliary residual is exactly the projection error from regressing its
own treatment on the other treatments and the controls. This characterization
does not assume the scalar FWL formula. -/
theorem auxiliaryResidual_projection (G : Submodule ℝ E) [G.HasOrthogonalProjection]
    (X : k → E) [Invertible (Matrix.gram ℝ (residualized G X))] (j : k) :
    X j - auxiliaryResidual G X j ∈ auxiliaryControls G X j ∧
      ∀ g ∈ auxiliaryControls G X j, inner ℝ (auxiliaryResidual G X j) g = 0 := by
  refine ⟨regressor_sub_auxiliaryResidual_mem G X j, ?_⟩
  intro g hg
  rw [auxiliaryResidual, real_inner_smul_left,
    dualRegressor_inner_auxiliaryControls G X j hg, mul_zero]

/-- Whenever expressed through Mathlib's orthogonal projection, the auxiliary
residual agrees with the projection error. -/
theorem auxiliaryResidual_eq_sub_projection (G : Submodule ℝ E)
    [G.HasOrthogonalProjection] (X : k → E)
    [Invertible (Matrix.gram ℝ (residualized G X))] (j : k)
    [(auxiliaryControls G X j).HasOrthogonalProjection] :
    auxiliaryResidual G X j = X j - (auxiliaryControls G X j).starProjection (X j) := by
  have h := auxiliaryResidual_projection G X j
  have hp := Submodule.eq_starProjection_of_mem_of_inner_eq_zero (u := X j) h.1 (by
    simpa only [sub_sub_cancel] using h.2)
  rw [hp, sub_sub_cancel]

section Probability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [DecidableEq k] in
private theorem coe_predictor_ae (X : k → Lp ℝ 2 μ) (b : k → ℝ) :
    (fun ω => predictor X b ω) =ᵐ[μ] fun ω => ∑ j, b j * X j ω := by
  classical
  have hsum : ∀ s : Finset k, (fun ω => (∑ j ∈ s, b j • X j) ω) =ᵐ[μ]
      fun ω => ∑ j ∈ s, b j * X j ω := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Lp.coeFn_zero ℝ 2 μ
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (b j • X j) (∑ i ∈ s, b i • X i),
        Lp.coeFn_smul (b j) (X j), ih] with ω ha hb hs
      change (b j • X j + ∑ i ∈ s, b i • X i) ω =
        (b j • X j) ω + (∑ i ∈ s, b i • X i) ω at ha
      exact ha.trans (congrArg₂ (· + ·) hb hs)
  exact hsum Finset.univ

omit [DecidableEq k] in
/-- The Hilbert-space criterion is the actual integral of squared prediction
error, using the random-variable representatives of the regressors and controls. -/
theorem loss_eq_integral (X : k → Lp ℝ 2 μ) (Y g : Lp ℝ 2 μ) (b : k → ℝ) :
    ‖Y - predictor X b - g‖ ^ 2 =
      ∫ ω, (Y ω - (∑ j, b j * X j ω) - g ω) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (Y - predictor X b) g,
    Lp.coeFn_sub Y (predictor X b), coe_predictor_ae X b] with ω h₁ h₂ h₃
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [h₁, Pi.sub_apply, h₂, Pi.sub_apply, h₃]

/-- Population FWL in expected-square-error notation. No causal restrictions
are used: the result applies to any square-integrable outcome and regressors. -/
theorem minimizes_expected_sq_error (G : Submodule ℝ (Lp ℝ 2 μ))
    [G.HasOrthogonalProjection] (X : k → Lp ℝ 2 μ) (Y : Lp ℝ 2 μ)
    [Invertible (Matrix.gram ℝ (residualized G X))]
    (b : k → ℝ) {g : Lp ℝ 2 μ} (hg : g ∈ G) :
    (∫ ω, (Y ω - (∑ j, coefficient G X Y j * X j ω) -
      controlFit G X Y (coefficient G X Y) ω) ^ 2 ∂μ) ≤
    ∫ ω, (Y ω - (∑ j, b j * X j ω) - g ω) ^ 2 ∂μ := by
  rw [← loss_eq_integral, ← loss_eq_integral]
  exact minimizes G X Y b hg

end Probability

end HansenEconometrics.PopulationFWL
