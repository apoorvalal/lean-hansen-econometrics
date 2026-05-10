import applications.Angrist1998

open scoped Matrix

namespace HansenEconometrics
namespace Applications
namespace MultipleTreatments

open Matrix

variable {c k : Type*}
variable [Fintype c] [Fintype k] [DecidableEq k]

/--
Within-cell covariance matrix of mutually exclusive treatment indicators, omitting
the control arm. If `p x j` is the cell propensity for active arm `j`, then the
diagonal entry is `p_j - p_j^2` and off-diagonal entry is `-p_j p_l`.
-/
noncomputable def cellTreatmentCovariance (p : c → k → ℝ) (x : c) : Matrix k k ℝ :=
  fun i j => (if i = j then p x i else 0) - p x i * p x j

/-- Aggregate residual covariance matrix of the treatment-indicator vector. -/
noncomputable def residualTreatmentCovariance
    (cellMass : c → ℝ) (p : c → k → ℝ) : Matrix k k ℝ :=
  ∑ x : c, cellMass x • cellTreatmentCovariance p x

/--
Population coefficient vector from the saturated simultaneous regression with
all active treatment indicators on the right-hand side.
-/
noncomputable def simultaneousCoefficient
    (cellMass : c → ℝ) (p τ : c → k → ℝ)
    [Invertible (residualTreatmentCovariance cellMass p)] : k → ℝ :=
  ⅟ (residualTreatmentCovariance cellMass p) *ᵥ
    ∑ x : c, cellMass x • (cellTreatmentCovariance p x *ᵥ τ x)

/--
Cell weight attached to treatment `l`'s cell effect in coefficient `j`.
For `j = l` this is the own-treatment block; for `j ≠ l` this is a
contamination block.
-/
noncomputable def simultaneousWeight
    (cellMass : c → ℝ) (p : c → k → ℝ)
    [Invertible (residualTreatmentCovariance cellMass p)] (j l : k) (x : c) : ℝ :=
  cellMass x * ((⅟ (residualTreatmentCovariance cellMass p) *
    cellTreatmentCovariance p x) j l)

omit [DecidableEq k] in
private theorem mulVec_sum_smul_mulVec
    (A : Matrix k k ℝ) (cellMass : c → ℝ)
    (B : c → Matrix k k ℝ) (v : c → k → ℝ) :
    A *ᵥ (∑ x : c, cellMass x • (B x *ᵥ v x)) =
      ∑ x : c, cellMass x • ((A * B x) *ᵥ v x) := by
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]

omit [DecidableEq k] in
private theorem matrix_mul_sum_smul_apply
    (A : Matrix k k ℝ) (cellMass : c → ℝ)
    (B : c → Matrix k k ℝ) (j l : k) :
    (A * ∑ x : c, cellMass x • B x) j l =
      ∑ x : c, cellMass x * (A * B x) j l := by
  rw [Matrix.mul_sum]
  simp [Matrix.sum_apply, Matrix.mul_apply, Finset.mul_sum,
    mul_left_comm]

omit [Fintype c] [Fintype k] in
@[simp] theorem cellTreatmentCovariance_apply
    (p : c → k → ℝ) (x : c) (j l : k) :
    cellTreatmentCovariance p x j l =
      (if j = l then p x j else 0) - p x j * p x l := by
  simp [cellTreatmentCovariance]

omit [Fintype c] [Fintype k] in
theorem cellTreatmentCovariance_apply_self
    (p : c → k → ℝ) (x : c) (j : k) :
    cellTreatmentCovariance p x j j = p x j * (1 - p x j) := by
  simp [cellTreatmentCovariance]
  ring

omit [Fintype c] [Fintype k] in
theorem cellTreatmentCovariance_apply_ne
    (p : c → k → ℝ) (x : c) {j l : k} (hjl : j ≠ l) :
    cellTreatmentCovariance p x j l = -p x j * p x l := by
  simp [cellTreatmentCovariance, hjl]

/--
Goldsmith-Pinkham--Hull--Kolesar finite-cell algebra, coefficient expansion.

The `j`th simultaneous-regression coefficient is a sum, over all arms `l` and
cells `x`, of `l`'s conditional treatment effect in cell `x` times the
corresponding simultaneous-regression weight.
-/
theorem simultaneousCoefficient_eq_sum_weights
    (cellMass : c → ℝ) (p τ : c → k → ℝ)
    [Invertible (residualTreatmentCovariance cellMass p)] (j : k) :
    simultaneousCoefficient cellMass p τ j =
      ∑ l : k, ∑ x : c, simultaneousWeight cellMass p j l x * τ x l := by
  rw [simultaneousCoefficient, mulVec_sum_smul_mulVec]
  simp only [simultaneousWeight, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Finset.sum_comm (s := (Finset.univ : Finset c)) (t := (Finset.univ : Finset k))
      (f := fun x l =>
        cellMass x * ((⅟ (residualTreatmentCovariance cellMass p) *
          cellTreatmentCovariance p x) j l) * τ x l))

/--
Goldsmith-Pinkham--Hull--Kolesar finite-cell algebra, weight normalization.

The weights in coefficient `j` on its own treatment effects sum to one, while
the weights on every other treatment's effects sum to zero.
-/
theorem simultaneousWeight_sum_cell
    (cellMass : c → ℝ) (p : c → k → ℝ)
    [Invertible (residualTreatmentCovariance cellMass p)] (j l : k) :
    ∑ x : c, simultaneousWeight cellMass p j l x = if j = l then 1 else 0 := by
  calc
    ∑ x : c, simultaneousWeight cellMass p j l x
        = (⅟ (residualTreatmentCovariance cellMass p) *
            residualTreatmentCovariance cellMass p) j l := by
          change ∑ x : c, simultaneousWeight cellMass p j l x =
            (⅟ (residualTreatmentCovariance cellMass p) *
              (∑ x : c, cellMass x • cellTreatmentCovariance p x)) j l
          rw [matrix_mul_sum_smul_apply]
          simp [simultaneousWeight]
    _ = if j = l then 1 else 0 := by
      have hmul :
          ⅟ (residualTreatmentCovariance cellMass p) *
              residualTreatmentCovariance cellMass p =
            (1 : Matrix k k ℝ) :=
        invOf_mul_self (residualTreatmentCovariance cellMass p)
      rw [hmul]
      simp [Matrix.one_apply]

theorem simultaneousWeight_sum_cell_self
    (cellMass : c → ℝ) (p : c → k → ℝ)
    [Invertible (residualTreatmentCovariance cellMass p)] (j : k) :
    ∑ x : c, simultaneousWeight cellMass p j j x = 1 := by
  simpa using simultaneousWeight_sum_cell cellMass p j j

theorem simultaneousWeight_sum_cell_ne
    (cellMass : c → ℝ) (p : c → k → ℝ)
    [Invertible (residualTreatmentCovariance cellMass p)] {j l : k} (hjl : j ≠ l) :
    ∑ x : c, simultaneousWeight cellMass p j l x = 0 := by
  simpa [hjl] using simultaneousWeight_sum_cell cellMass p j l

namespace Lal

variable {g : Type*}
variable [Fintype g]

/-- Mass of cell `x` in the pairwise sample comparing control to active arm `k`. -/
def pairwiseCellMass (cellMass p0 pk : g → ℝ) (x : g) : ℝ :=
  cellMass x * (p0 x + pk x)

/-- Pairwise treatment propensity inside the control-versus-`k` comparison sample. -/
noncomputable def pairwisePropensity (p0 pk : g → ℝ) (x : g) : ℝ :=
  pk x / (p0 x + pk x)

/--
One-at-a-time regression coefficient for arm `k`, stated as a direct Angrist
binary-treatment regression inside the pairwise comparison sample.
-/
noncomputable def oneAtATimeCoefficient
    (cellMass p0 pk y0 yk : g → ℝ) : ℝ :=
  Angrist1998.cellRegressionCoefficient
    (pairwiseCellMass cellMass p0 pk) (pairwisePropensity p0 pk) y0 yk

/-- Pairwise overlap-weighted treatment effect targeted by one-at-a-time adjustment. -/
noncomputable def oneAtATimeOverlapEffect
    (cellMass p0 pk y0 yk : g → ℝ) : ℝ :=
  Angrist1998.overlapWeightedTreatmentEffect
    (pairwiseCellMass cellMass p0 pk) (pairwisePropensity p0 pk) y0 yk

/--
Lal one-at-a-time regression-adjustment target: after fixing one treatment arm
and comparing it to control, the coefficient is the Angrist overlap-weighted
average for that pairwise binary problem.
-/
theorem oneAtATimeCoefficient_eq_overlapEffect
    (cellMass p0 pk y0 yk : g → ℝ) :
    oneAtATimeCoefficient cellMass p0 pk y0 yk =
      oneAtATimeOverlapEffect cellMass p0 pk y0 yk := by
  unfold oneAtATimeCoefficient oneAtATimeOverlapEffect
  exact Angrist1998.cellRegressionCoefficient_eq_overlapWeightedTreatmentEffect
    (pairwiseCellMass cellMass p0 pk) (pairwisePropensity p0 pk) y0 yk

omit [Fintype g] in
/--
Pairwise overlap weights in original cell-probability notation. If the
control-or-treatment probability in a cell is nonzero, the pairwise overlap
mass equals `m_x p_0(x) p_k(x) / (p_0(x)+p_k(x))`.
-/
theorem pairwise_overlapWeight_eq_original
    (cellMass p0 pk : g → ℝ) (x : g) (hden : p0 x + pk x ≠ 0) :
    Angrist1998.overlapWeight
        (pairwiseCellMass cellMass p0 pk) (pairwisePropensity p0 pk) x =
      cellMass x * p0 x * pk x / (p0 x + pk x) := by
  unfold Angrist1998.overlapWeight pairwiseCellMass pairwisePropensity
  field_simp [hden]
  ring

/--
Difference between a treatment-specific weighted average and an ATE, written as
a covariance term when the normalized weight has mean one.
-/
theorem weightedAverage_eq_ate_add_covariance
    (cellMass weight τ : g → ℝ) :
    ∑ x : g, cellMass x * weight x * τ x =
      (∑ x : g, cellMass x * τ x) +
        (∑ x : g, cellMass x * (weight x - 1) * τ x) := by
  calc
    ∑ x : g, cellMass x * weight x * τ x
        = ∑ x : g, (cellMass x * τ x +
            (cellMass x * (weight x - 1) * τ x)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
    _ = (∑ x : g, cellMass x * τ x) +
        (∑ x : g, cellMass x * (weight x - 1) * τ x) := by
          rw [Finset.sum_add_distrib]

/--
Lal rank-accounting identity: the difference in weighted estimands equals the
ATE difference plus the difference in the two weighting covariance terms.
-/
theorem weightedRankingGap_eq_ateGap_add_covarianceGap
    (cellMass weightJ weightK τJ τK : g → ℝ) :
    (∑ x : g, cellMass x * weightJ x * τJ x) -
        (∑ x : g, cellMass x * weightK x * τK x) =
      ((∑ x : g, cellMass x * τJ x) - (∑ x : g, cellMass x * τK x)) +
        ((∑ x : g, cellMass x * (weightJ x - 1) * τJ x) -
          (∑ x : g, cellMass x * (weightK x - 1) * τK x)) := by
  rw [weightedAverage_eq_ate_add_covariance cellMass weightJ τJ,
    weightedAverage_eq_ate_add_covariance cellMass weightK τK]
  ring

end Lal

end MultipleTreatments
end Applications
end HansenEconometrics
