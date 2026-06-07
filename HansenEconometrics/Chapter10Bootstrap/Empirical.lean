import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.UniformOn
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.Chapter3Projections
import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.Chapter6Asymptotics
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 10 — Finite empirical distributions

Finite empirical distributions, jackknife identities, bootstrap inclusion
probabilities, and exact finite-resampling moments, together with the centered
empirical characteristic-function expansions used downstream.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section EmpiricalDistribution

variable {ι : Type*} [MeasurableSpace ι] [Fintype ι]

/-- Uniform sampling from a finite empirical support is normalized counting
measure. -/
theorem uniformOn_univ_eq_inv_card_smul_count :
    (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹) • Measure.count := by
  ext s hs
  rw [ProbabilityTheory.uniformOn_univ, Measure.smul_apply]
  simp [ENNReal.div_eq_inv_mul]

variable [MeasurableSingletonClass ι]

/-- Finite-sample empirical mean. -/
noncomputable def empiricalMean
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : ι → E) : E :=
  ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i

/-- Mean of a bootstrap resample indexed by `κ`.

The map `I ωs t` is the original observation selected by bootstrap draw `t` at
resampling point `ωs`.  For the ordinary nonparametric bootstrap, `Ωs` is a
finite function space and `I ωs t = ωs t`. -/
noncomputable def empiricalBootstrapResampleMean
    {κ : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : ι → E) (I : Ωs → κ → ι) (ωs : Ωs) : E :=
  ((Fintype.card κ : ℝ)⁻¹) • ∑ t, Y (I ωs t)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Leave-one-out sample mean for Hansen's jackknife discussion.

For observation `i`, this is the empirical mean of the sample with `i`
deleted, matching equation (10.2). -/
noncomputable def jackknifeLeaveOneOutMean
    [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : ι → E) (i : ι) : E :=
  ((Fintype.card (LeaveOneOutIndex i) : ℝ≥0∞)⁻¹).toReal •
    ∑ j : LeaveOneOutIndex i, Y j

/-- Mean of jackknife pseudo-sample estimators. -/
noncomputable def jackknifeMean
    [NormedAddCommGroup E] [NormedSpace ℝ E] (theta : ι → E) : E :=
  empiricalMean theta

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Hansen equation (10.1): Tukey's jackknife covariance estimator. -/
noncomputable def jackknifeCovariance
    {k : Type*} [Fintype k] (theta : ι → k → ℝ) : Matrix k k ℝ :=
  fun a b =>
    (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) *
      ∑ i, (theta i a - jackknifeMean theta a) *
        (theta i b - jackknifeMean theta b)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Cardinality of the row-deleted jackknife index. -/
theorem card_leaveOneOutIndex [DecidableEq ι] (i : ι) :
    Fintype.card (LeaveOneOutIndex i) = Fintype.card ι - 1 :=
  Set.card_ne_eq i

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Hansen equation (10.2): the leave-one-out mean written in terms of the
full-sample mean and the deleted observation. -/
theorem jackknifeLeaveOneOutMean_eq
    [DecidableEq ι] [Nontrivial ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : ι → E) (i : ι) :
    jackknifeLeaveOneOutMean Y i =
      ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) • empiricalMean Y -
        (((Fintype.card ι : ℝ) - 1)⁻¹) • Y i := by
  classical
  have hsum := Fintype.sum_eq_add_sum_subtype_ne Y i
  have hcard := card_leaveOneOutIndex (ι := ι) i
  have hlt : (1 : ℕ) < Fintype.card ι := Fintype.one_lt_card
  have hle : (1 : ℕ) ≤ Fintype.card ι := hlt.le
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have hltR : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hlt
    linarith
  simp only [jackknifeLeaveOneOutMean, empiricalMean, hcard,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Nat.cast_sub hle]
  simp only [Nat.cast_one]
  calc
    (((Fintype.card ι : ℝ) - 1)⁻¹) • ∑ j : LeaveOneOutIndex i, Y j =
        (((Fintype.card ι : ℝ) - 1)⁻¹) • ((∑ j : ι, Y j) - Y i) := by
          rw [hsum]
          simp [add_sub_cancel_left]
    _ =
        ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) •
            (((Fintype.card ι : ℝ)⁻¹) • ∑ j : ι, Y j) -
          (((Fintype.card ι : ℝ) - 1)⁻¹) • Y i := by
          rw [smul_sub, smul_smul]
          congr 1
          field_simp [hn, hn1]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The average of the leave-one-out sample means is the full-sample mean. -/
theorem jackknifeMean_leaveOneOutMean_eq_empiricalMean
    [DecidableEq ι] [Nontrivial ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : ι → E) :
    jackknifeMean (fun i => jackknifeLeaveOneOutMean Y i) = empiricalMean Y := by
  classical
  have hlt : (1 : ℕ) < Fintype.card ι := Fintype.one_lt_card
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have hltR : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hlt
    linarith
  simp only [jackknifeMean, empiricalMean, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  calc
    ((Fintype.card ι : ℝ)⁻¹) •
        ∑ i : ι, jackknifeLeaveOneOutMean Y i =
        ((Fintype.card ι : ℝ)⁻¹) •
          ∑ i : ι,
            (((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) •
              (((Fintype.card ι : ℝ)⁻¹) • ∑ j : ι, Y j) -
                (((Fintype.card ι : ℝ) - 1)⁻¹) • Y i) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [jackknifeLeaveOneOutMean_eq (Y := Y) i]
          simp [empiricalMean, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    _ = ((Fintype.card ι : ℝ)⁻¹) • ∑ j : ι, Y j := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.smul_sum,
            Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ (Fintype.card ι)]
          simp only [smul_smul]
          rw [← sub_smul]
          rw [← one_smul ℝ (∑ j : ι, Y j)]
          congr 1
          field_simp [hn, hn1]
          simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Hansen's displayed identity after (10.2): each leave-one-out mean differs
from the full-sample mean by `(Ybar - Yᵢ)/(n-1)`. -/
theorem jackknifeLeaveOneOutMean_sub_empiricalMean_eq
    [DecidableEq ι] [Nontrivial ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : ι → E) (i : ι) :
    jackknifeLeaveOneOutMean Y i - empiricalMean Y =
      (((Fintype.card ι : ℝ) - 1)⁻¹) • (empiricalMean Y - Y i) := by
  classical
  have hlt : (1 : ℕ) < Fintype.card ι := Fintype.one_lt_card
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have hltR : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hlt
    linarith
  rw [jackknifeLeaveOneOutMean_eq (Y := Y) i]
  calc
    ((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) • empiricalMean Y -
        (((Fintype.card ι : ℝ) - 1)⁻¹) • Y i - empiricalMean Y =
      (((Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 1)) • empiricalMean Y -
        empiricalMean Y) - (((Fintype.card ι : ℝ) - 1)⁻¹) • Y i := by
        abel
    _ = (((Fintype.card ι : ℝ) - 1)⁻¹) • empiricalMean Y -
        (((Fintype.card ι : ℝ) - 1)⁻¹) • Y i := by
        congr 1
        rw [← one_smul ℝ (empiricalMean Y)]
        simp only [smul_smul]
        rw [← sub_smul]
        congr 1
        field_simp [hn, hn1]
        ring
    _ = (((Fintype.card ι : ℝ) - 1)⁻¹) • (empiricalMean Y - Y i) :=
        (smul_sub _ _ _).symm

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Hansen equation (10.3): for the sample mean, Tukey's jackknife covariance
equals the conventional covariance estimator for the variance of the mean. -/
theorem jackknifeCovariance_leaveOneOutMean_eq_sampleMeanCovariance
    [DecidableEq ι] [Nontrivial ι] {k : Type*} [Fintype k]
    (Y : ι → k → ℝ) :
    jackknifeCovariance (fun i => jackknifeLeaveOneOutMean Y i) =
      fun a b =>
        ((Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) - 1)⁻¹) *
          ∑ i, (empiricalMean Y a - Y i a) * (empiricalMean Y b - Y i b) := by
  classical
  have hlt : (1 : ℕ) < Fintype.card ι := Fintype.one_lt_card
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have hltR : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hlt
    linarith
  ext a b
  have hmean :=
    jackknifeMean_leaveOneOutMean_eq_empiricalMean (Y := Y)
  simp only [jackknifeCovariance, hmean]
  have hdiff (i : ι) (c : k) :
      jackknifeLeaveOneOutMean Y i c - empiricalMean Y c =
        (((Fintype.card ι : ℝ) - 1)⁻¹) * (empiricalMean Y c - Y i c) := by
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      congr_fun (jackknifeLeaveOneOutMean_sub_empiricalMean_eq (Y := Y) i) c
  simp_rw [hdiff]
  have hterm (i : ι) :
      (((Fintype.card ι : ℝ) - 1)⁻¹ * (empiricalMean Y a - Y i a)) *
          (((Fintype.card ι : ℝ) - 1)⁻¹ * (empiricalMean Y b - Y i b)) =
        (((Fintype.card ι : ℝ) - 1)⁻¹ * ((Fintype.card ι : ℝ) - 1)⁻¹) *
          ((empiricalMean Y a - Y i a) * (empiricalMean Y b - Y i b)) := by
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  field_simp [hn, hn1]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Matrix form of the jackknife covariance definition. -/
private theorem jackknifeCovariance_eq_scaled_centered_outer
    {k : Type*} [Fintype k] (theta : ι → k → ℝ) :
    jackknifeCovariance theta =
      (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) •
        ∑ i, Matrix.vecMulVec (theta i - jackknifeMean theta)
          (theta i - jackknifeMean theta) := by
  ext a b
  simp [jackknifeCovariance, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.sub_apply]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Centered outer-product expansion for finite empirical means, using the
`mean - observation` orientation that appears in Hansen's jackknife algebra. -/
private theorem sum_vecMulVec_empiricalMean_sub_eq
    [Nonempty ι] {k : Type*} [Fintype k] (Z : ι → k → ℝ) :
    (∑ i, Matrix.vecMulVec (empiricalMean Z - Z i) (empiricalMean Z - Z i)) =
      ∑ i, Matrix.vecMulVec (Z i) (Z i) -
        (Fintype.card ι : ℝ) • Matrix.vecMulVec (empiricalMean Z) (empiricalMean Z) := by
  classical
  ext a b
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum_a : ∑ i : ι, Z i a = (Fintype.card ι : ℝ) * empiricalMean Z a := by
    simp [empiricalMean, smul_eq_mul]
  have hsum_b : ∑ i : ι, Z i b = (Fintype.card ι : ℝ) * empiricalMean Z b := by
    simp [empiricalMean, smul_eq_mul]
  calc
    (∑ i, Matrix.vecMulVec (empiricalMean Z - Z i) (empiricalMean Z - Z i)) a b =
        ∑ i, (empiricalMean Z a - Z i a) * (empiricalMean Z b - Z i b) := by
          simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.sub_apply]
    _ = ∑ i, (Z i a * Z i b - Z i a * empiricalMean Z b -
          empiricalMean Z a * Z i b + empiricalMean Z a * empiricalMean Z b) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = (∑ i, Z i a * Z i b) -
          (∑ i, Z i a) * empiricalMean Z b -
          empiricalMean Z a * (∑ i, Z i b) +
          (Fintype.card ι : ℝ) * (empiricalMean Z a * empiricalMean Z b) := by
          simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul,
            Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ = (∑ i, Z i a * Z i b) -
          (Fintype.card ι : ℝ) * (empiricalMean Z a * empiricalMean Z b) := by
          rw [hsum_a, hsum_b]
          ring
    _ =
        (∑ i, Matrix.vecMulVec (Z i) (Z i) -
          (Fintype.card ι : ℝ) • Matrix.vecMulVec (empiricalMean Z) (empiricalMean Z)) a b := by
          simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
            Matrix.sub_apply]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Hansen equation (10.5) score mean
`\tilde\mu = n^{-1}\sum_i X_i \tilde e_i`, stated with the leave-one-out
prediction errors from Chapter 3. -/
noncomputable def olsLeaveOneOutScoreMean
    [DecidableEq ι] {k : Type*} [Fintype k] [DecidableEq k]
    (X : Matrix ι k ℝ) (y : ι → ℝ)
    [Invertible (Xᵀ * X)]
    (hloo : ∀ i : ι, Invertible (leaveOneOutGram X i)) : k → ℝ :=
  empiricalMean fun i : ι =>
    letI : Invertible (leaveOneOutGram X i) := hloo i
    leaveOneOutResidual X y i • X i

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The family of OLS coefficients obtained by deleting one observation. -/
noncomputable def olsLeaveOneOutBetaFamily
    [DecidableEq ι] {k : Type*} [Fintype k] [DecidableEq k]
    (X : Matrix ι k ℝ) (y : ι → ℝ)
    (hloo : ∀ i : ι, Invertible (leaveOneOutGram X i)) : ι → k → ℝ :=
  fun i =>
    letI : Invertible (leaveOneOutGram X i) := hloo i
    leaveOneOutBeta X y i

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Influence vector `(X'X)^{-1}X_i\tilde e_i` in Hansen's OLS jackknife
calculation. -/
noncomputable def olsLeaveOneOutInfluence
    [DecidableEq ι] {k : Type*} [Fintype k] [DecidableEq k]
    (X : Matrix ι k ℝ) (y : ι → ℝ)
    [Invertible (Xᵀ * X)]
    (hloo : ∀ i : ι, Invertible (leaveOneOutGram X i)) (i : ι) : k → ℝ :=
  letI : Invertible (leaveOneOutGram X i) := hloo i
  leaveOneOutResidual X y i • (⅟ (Xᵀ * X) *ᵥ X i)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The mean of the OLS leave-one-out influence vectors is
`(X'X)^{-1}\tilde\mu`. -/
theorem empiricalMean_olsLeaveOneOutInfluence_eq_invGram_mulVec_scoreMean
    [DecidableEq ι] {k : Type*} [Fintype k] [DecidableEq k]
    (X : Matrix ι k ℝ) (y : ι → ℝ)
    [Invertible (Xᵀ * X)]
    (hloo : ∀ i : ι, Invertible (leaveOneOutGram X i)) :
    empiricalMean (olsLeaveOneOutInfluence X y hloo) =
      ⅟ (Xᵀ * X) *ᵥ olsLeaveOneOutScoreMean X y hloo := by
  simp only [empiricalMean, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    olsLeaveOneOutInfluence, olsLeaveOneOutScoreMean]
  rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  letI : Invertible (leaveOneOutGram X i) := hloo i
  rw [Matrix.mulVec_smul]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Leave-one-out coefficient deviations equal the centered influence
deviations used in Hansen equation (10.5). -/
theorem leaveOneOutBeta_sub_jackknifeMean_eq_influenceMean_sub
    [DecidableEq ι] [Nontrivial ι] {k : Type*} [Fintype k] [DecidableEq k]
    (X : Matrix ι k ℝ) (y : ι → ℝ)
    [Invertible (Xᵀ * X)]
    (hloo : ∀ i : ι, Invertible (leaveOneOutGram X i)) (i : ι) :
    olsLeaveOneOutBetaFamily X y hloo i -
        jackknifeMean (olsLeaveOneOutBetaFamily X y hloo) =
      empiricalMean (olsLeaveOneOutInfluence X y hloo) -
        olsLeaveOneOutInfluence X y hloo i := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext a
  simp only [Pi.sub_apply]
  have hbeta (j : ι) :
      olsLeaveOneOutBetaFamily X y hloo j =
        olsBeta X y - olsLeaveOneOutInfluence X y hloo j := by
    letI : Invertible (leaveOneOutGram X j) := hloo j
    unfold olsLeaveOneOutBetaFamily olsLeaveOneOutInfluence
    rw [leaveOneOutBeta_eq_olsBeta_sub_invGram_mulVec]
  simp only [jackknifeMean, empiricalMean, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [hbeta i]
  have hsum :
      ∑ j : ι, olsLeaveOneOutBetaFamily X y hloo j =
        (Fintype.card ι : ℝ) • olsBeta X y -
          ∑ j : ι, olsLeaveOneOutInfluence X y hloo j := by
    calc
      ∑ j : ι, olsLeaveOneOutBetaFamily X y hloo j =
          ∑ j : ι, (olsBeta X y - olsLeaveOneOutInfluence X y hloo j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [hbeta j]
      _ = (Fintype.card ι : ℝ) • olsBeta X y -
            ∑ j : ι, olsLeaveOneOutInfluence X y hloo j := by
            simp [Finset.sum_sub_distrib, Finset.sum_const,
              ← Nat.cast_smul_eq_nsmul ℝ (Fintype.card ι)]
  rw [hsum]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hn]
  ring_nf

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The uncentered OLS leave-one-out influence outer-product sum is the HC3
covariance estimator when the leave-one-out residuals are written as prediction
errors. -/
theorem sum_vecMulVec_olsLeaveOneOutInfluence_eq_HC3
    [DecidableEq ι] {k : Type*} [Fintype k] [DecidableEq k]
    (X : Matrix ι k ℝ) (y : ι → ℝ)
    [Invertible (Xᵀ * X)]
    (hloo : ∀ i : ι, Invertible (leaveOneOutGram X i))
    (hdenom : ∀ i : ι, 1 - leverageValue X i ≠ 0) :
    (∑ i, Matrix.vecMulVec (olsLeaveOneOutInfluence X y hloo i)
        (olsLeaveOneOutInfluence X y hloo i)) =
      olsHuberWhiteHC3VarianceEstimator X y := by
  classical
  ext a b
  rw [olsHuberWhiteHC3VarianceEstimator]
  rw [olsConditionalVarianceMatrix_diagonal_apply]
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  letI : Invertible (leaveOneOutGram X i) := hloo i
  have hdenom' : 1 - hatMatrix X i i ≠ 0 := by
    simpa [leverageValue] using hdenom i
  rw [show olsLeaveOneOutInfluence X y hloo i =
      leaveOneOutResidual X y i • (⅟ (Xᵀ * X) *ᵥ X i) by rfl]
  rw [leaveOneOutResidual_eq_inv_one_sub_leverage_mul_residual X y i (hdenom i)]
  simp [leverageValue, smul_eq_mul, Matrix.mulVec, Matrix.mul_apply,
    Matrix.transpose_apply, dotProduct]
  field_simp [hdenom']

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Hansen equation (10.5): the OLS leave-one-out jackknife covariance equals
the HC3 covariance estimator less the finite-sample mean-adjustment outer
product. -/
theorem jackknifeCovariance_leaveOneOutBeta_eq_HC3_sub_meanAdjustment
    [DecidableEq ι] [Nontrivial ι] {k : Type*} [Fintype k] [DecidableEq k]
    (X : Matrix ι k ℝ) (y : ι → ℝ)
    [Invertible (Xᵀ * X)]
    (hloo : ∀ i : ι, Invertible (leaveOneOutGram X i))
    (hdenom : ∀ i : ι, 1 - leverageValue X i ≠ 0) :
    jackknifeCovariance (olsLeaveOneOutBetaFamily X y hloo) =
      (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) •
          olsHuberWhiteHC3VarianceEstimator X y -
        ((Fintype.card ι : ℝ) - 1) •
          Matrix.vecMulVec (empiricalMean (olsLeaveOneOutInfluence X y hloo))
            (empiricalMean (olsLeaveOneOutInfluence X y hloo)) := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [jackknifeCovariance_eq_scaled_centered_outer]
  have hdev (i : ι) :
      olsLeaveOneOutBetaFamily X y hloo i -
          jackknifeMean (olsLeaveOneOutBetaFamily X y hloo) =
        empiricalMean (olsLeaveOneOutInfluence X y hloo) -
          olsLeaveOneOutInfluence X y hloo i :=
    leaveOneOutBeta_sub_jackknifeMean_eq_influenceMean_sub X y hloo i
  simp_rw [hdev]
  rw [sum_vecMulVec_empiricalMean_sub_eq]
  rw [sum_vecMulVec_olsLeaveOneOutInfluence_eq_HC3 X y hloo hdenom]
  ext a b
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply]
  field_simp [hn]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Dot-product projection of a finite empirical mean. -/
theorem empiricalMean_dotProduct
    {k : Type*} [Fintype k]
    (Y : ι → k → ℝ) (a : k → ℝ) :
    empiricalMean Y ⬝ᵥ a = empiricalMean (fun i => Y i ⬝ᵥ a) := by
  simp [empiricalMean, smul_dotProduct, sum_dotProduct, smul_eq_mul]

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Dot-product projection of a finite bootstrap resample mean. -/
theorem empiricalBootstrapResampleMean_dotProduct
    {κ : Type*} [Fintype κ] {Ωs : Type*}
    {k : Type*} [Fintype k]
    (Y : ι → k → ℝ) (I : Ωs → κ → ι) (ωs : Ωs) (a : k → ℝ) :
    empiricalBootstrapResampleMean Y I ωs ⬝ᵥ a =
      empiricalBootstrapResampleMean (fun i => Y i ⬝ᵥ a) I ωs := by
  simp [empiricalBootstrapResampleMean, smul_dotProduct, sum_dotProduct, smul_eq_mul]

/-- Empirical mean identity for one bootstrap draw.

For any finite empirical support, integrating a statistic under the uniform
resampling law equals the finite-sample average.  This is the measure-theoretic
form of Hansen's equations (10.10) and (10.12). -/
theorem integral_uniformOn_univ_eq_card_inv_smul_sum
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ i, Y i ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i := by
  rw [uniformOn_univ_eq_inv_card_smul_count, integral_smul_measure, integral_count]

/-- Empirical mean identity using the canonical `empiricalMean` API. -/
theorem integral_uniformOn_univ_eq_empiricalMean
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ i, Y i ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      empiricalMean Y :=
  integral_uniformOn_univ_eq_card_inv_smul_sum Y

/-- Centered empirical one-draw mean is zero under the finite uniform law. -/
theorem integral_uniformOn_univ_sub_empiricalMean_eq_zero
    [Nonempty ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ i, Y i - empiricalMean Y
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      0 := by
  let P : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have hY : Integrable Y P := Integrable.of_finite
  have hmean : Integrable (fun _ : ι => empiricalMean Y) P := integrable_const _
  rw [integral_sub hY hmean]
  rw [integral_uniformOn_univ_eq_empiricalMean (Y := Y)]
  simp [P, empiricalMean]

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Uniform law on finite resampling functions is the product of empirical
uniform laws.

This is the measure-level iid structure behind ordinary finite
nonparametric-bootstrap resampling. -/
theorem uniformOn_fun_univ_eq_pi_uniformOn_univ
    {κ ι : Type*} [MeasurableSpace ι] [Fintype κ] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass (κ → ι)] :
    (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      Measure.pi
        (fun _ : κ =>
          (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  simpa using
    (ProbabilityTheory.uniformOn_pi (Ω := ι) (ι := κ)
      (f := fun _ : κ => (Set.univ : Set ι)))

/-- Hansen equation (10.6): displayed probability that one fixed observation is
included at least once in an `n`-draw bootstrap sample from `n` observations.

The expression is totalized at `n = 0`; the asymptotic result below is the
textbook statement. -/
noncomputable def bootstrapObservationInclusionProbability (n : ℕ) : ℝ :=
  1 - (1 - (n : ℝ)⁻¹) ^ n

theorem bootstrapObservationInclusionProbability_eq (n : ℕ) :
    bootstrapObservationInclusionProbability n =
      1 - (1 - (1 : ℝ) / n) ^ n := by
  simp [bootstrapObservationInclusionProbability, div_eq_mul_inv]

/-- Hansen equation (10.6): `1 - (1 - 1/n)^n → 1 - e^{-1}`. -/
theorem bootstrapObservationInclusionProbability_tendsto :
    Tendsto bootstrapObservationInclusionProbability atTop
      (𝓝 (1 - Real.exp (-1))) := by
  have hpow :
      Tendsto (fun n : ℕ => (1 - (n : ℝ)⁻¹) ^ n) atTop
        (𝓝 (Real.exp (-1))) := by
    simpa [sub_eq_add_neg, neg_div] using
      (Real.tendsto_one_add_div_pow_exp (-1))
  have hsub :
      Tendsto (fun n : ℕ => (1 : ℝ) - (1 - (n : ℝ)⁻¹) ^ n) atTop
        (𝓝 ((1 : ℝ) - Real.exp (-1))) := by
    exact
      (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) from
        tendsto_const_nhds).sub hpow
  simpa [bootstrapObservationInclusionProbability] using hsub

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Coordinate projections of the finite ordinary-bootstrap resampling space
are independent under the uniform law.

This exposes the iid coordinate fact used implicitly in the finite covariance
proofs and needed by the ordinary-bootstrap CLT route. -/
theorem iIndepFun_uniformOn_fun_eval
    {κ ι : Type*} [MeasurableSpace ι] [Finite κ] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass (κ → ι)] :
    iIndepFun (fun t (ωs : κ → ι) => ωs t)
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
        Measure (κ → ι)) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : Fintype ι := Fintype.ofFinite ι
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have hP :
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        Measure.pi (fun _ : κ => Pι) := by
    simpa [Pι] using
      (uniformOn_fun_univ_eq_pi_uniformOn_univ (κ := κ) (ι := ι))
  rw [hP]
  simpa [Pι] using
    (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : κ => Pι) (X := fun _ : κ => id)
      (fun _ => aemeasurable_id))

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Each coordinate projection of the finite ordinary-bootstrap resampling
space has the empirical uniform law. -/
theorem identDistrib_uniformOn_fun_eval
    {κ ι : Type*} [MeasurableSpace ι] [Finite κ] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass ι] [MeasurableSingletonClass (κ → ι)] (t : κ) :
    IdentDistrib
      (fun ωs : κ → ι => ωs t) (fun i : ι => i)
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
        Measure (κ → ι))
      (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : Fintype ι := Fintype.ofFinite ι
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have hP :
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        Measure.pi (fun _ : κ => Pι) := by
    simpa [Pι] using
      (uniformOn_fun_univ_eq_pi_uniformOn_univ (κ := κ) (ι := ι))
  have hmap :
      Measure.map (Function.eval t)
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
            Measure (κ → ι)) =
        Pι := by
    rw [hP]
    exact (measurePreserving_eval (μ := fun _ : κ => Pι) t).map_eq
  exact
    { aemeasurable_fst := (measurable_pi_apply t).aemeasurable
      aemeasurable_snd := aemeasurable_id
      map_eq := by simpa [Pι] using hmap }

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Transformed ordinary-bootstrap draws are independent coordinates under the
finite uniform resampling law. -/
theorem iIndepFun_uniformOn_fun_eval_comp
    {κ ι E : Type*} [MeasurableSpace ι] [MeasurableSpace E]
    [Finite κ] [Finite ι] [Nonempty ι] [MeasurableSingletonClass ι]
    [MeasurableSingletonClass (κ → ι)]
    (g : ι → E) (hg : Measurable g) :
    iIndepFun (fun t (ωs : κ → ι) => g (ωs t))
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
        Measure (κ → ι)) :=
  (iIndepFun_uniformOn_fun_eval (κ := κ) (ι := ι)).comp
    (fun _ => g) (fun _ => hg)

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Transformed ordinary-bootstrap draws are identically distributed with the
same transform under the empirical uniform law. -/
theorem identDistrib_uniformOn_fun_eval_comp
    {κ ι E : Type*} [MeasurableSpace ι] [MeasurableSpace E]
    [Finite κ] [Finite ι] [Nonempty ι] [MeasurableSingletonClass ι]
    [MeasurableSingletonClass (κ → ι)]
    (g : ι → E) (hg : Measurable g) (t : κ) :
    IdentDistrib
      (fun ωs : κ → ι => g (ωs t)) g
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
        Measure (κ → ι))
      (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) :=
  (identDistrib_uniformOn_fun_eval (κ := κ) (ι := ι) t).comp hg

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Centered transformed ordinary-bootstrap draws are independent coordinates
under the finite uniform resampling law.

This is the iid summand shape used in Hansen's ordinary-bootstrap CLT proof:
each draw is centered at the finite empirical mean. -/
theorem iIndepFun_uniformOn_fun_eval_sub_empiricalMean
    {κ ι E : Type*} [MeasurableSpace ι] [MeasurableSpace E]
    [Finite κ] [Fintype ι] [Nonempty ι] [MeasurableSingletonClass ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : ι → E) :
    iIndepFun (fun t (ωs : κ → ι) => Y (ωs t) - empiricalMean Y)
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
        Measure (κ → ι)) := by
  simpa using
    (iIndepFun_uniformOn_fun_eval_comp (κ := κ) (ι := ι) (E := E)
      (g := fun i : ι => Y i - empiricalMean Y)
      (measurable_of_finite (fun i : ι => Y i - empiricalMean Y)))

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Centered transformed ordinary-bootstrap draws are identically distributed
with their empirical-support counterpart.

This packages the one-draw law for the centered summands
`Y_i^* - Ybar` used by the ordinary-bootstrap CLT route. -/
theorem identDistrib_uniformOn_fun_eval_sub_empiricalMean
    {κ ι E : Type*} [MeasurableSpace ι] [MeasurableSpace E]
    [Finite κ] [Fintype ι] [Nonempty ι] [MeasurableSingletonClass ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : ι → E) (t : κ) :
    IdentDistrib
      (fun ωs : κ → ι => Y (ωs t) - empiricalMean Y)
      (fun i : ι => Y i - empiricalMean Y)
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
        Measure (κ → ι))
      (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) := by
  simpa using
    (identDistrib_uniformOn_fun_eval_comp (κ := κ) (ι := ι) (E := E)
      (g := fun i : ι => Y i - empiricalMean Y)
      (measurable_of_finite (fun i : ι => Y i - empiricalMean Y)) t)

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Scaled centered ordinary-bootstrap draws are independent coordinates under
the finite uniform resampling law.

This is the exact one-draw array shape behind CLT normalizations such as
`n^{-1/2} (Y_i^* - Ybar)`. -/
theorem iIndepFun_uniformOn_fun_eval_smul_sub_empiricalMean
    {κ ι E : Type*} [MeasurableSpace ι] [MeasurableSpace E]
    [Finite κ] [Fintype ι] [Nonempty ι] [MeasurableSingletonClass ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (Y : ι → E) :
    iIndepFun (fun t (ωs : κ → ι) => c • (Y (ωs t) - empiricalMean Y))
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
        Measure (κ → ι)) := by
  simpa using
    (iIndepFun_uniformOn_fun_eval_comp (κ := κ) (ι := ι) (E := E)
      (g := fun i : ι => c • (Y i - empiricalMean Y))
      (measurable_of_finite (fun i : ι => c • (Y i - empiricalMean Y))))

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Scaled centered ordinary-bootstrap draws are identically distributed with
their empirical-support counterpart.

This packages the one-draw law for normalized centered summands used by the
ordinary-bootstrap CLT route. -/
theorem identDistrib_uniformOn_fun_eval_smul_sub_empiricalMean
    {κ ι E : Type*} [MeasurableSpace ι] [MeasurableSpace E]
    [Finite κ] [Fintype ι] [Nonempty ι] [MeasurableSingletonClass ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (Y : ι → E) (t : κ) :
    IdentDistrib
      (fun ωs : κ → ι => c • (Y (ωs t) - empiricalMean Y))
      (fun i : ι => c • (Y i - empiricalMean Y))
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
        Measure (κ → ι))
      (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) := by
  simpa using
    (identDistrib_uniformOn_fun_eval_comp (κ := κ) (ι := ι) (E := E)
      (g := fun i : ι => c • (Y i - empiricalMean Y))
      (measurable_of_finite (fun i : ι => c • (Y i - empiricalMean Y))) t)

/-- Characteristic function of the sum of scaled centered ordinary-bootstrap
draws.

Under the finite uniform resampling law on `κ → ι`, the scaled centered draws
are iid with empirical one-draw law, so the characteristic function of their
sum is the corresponding one-draw characteristic function raised to `#κ`. -/
theorem charFun_sum_uniformOn_fun_eval_smul_sub_empiricalMean_eq_pow
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (c : ℝ) (Y : ι → ℝ) (u : ℝ) :
    charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
          Measure (κ → ι)).map
          (fun ωs => ∑ t : κ, c • (Y (ωs t) - empiricalMean Y)))) u =
      (charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι).map
          (fun i => c • (Y i - empiricalMean Y)))) u) ^ Fintype.card κ := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => c • (Y (ωs t) - empiricalMean Y)
  let G : ι → ℝ := fun i => c • (Y i - empiricalMean Y)
  have hIndep : iIndepFun X Pκ := by
    simpa [X, Pκ] using
      (iIndepFun_uniformOn_fun_eval_smul_sub_empiricalMean
        (κ := κ) (ι := ι) (E := ℝ) c Y)
  have hMeas : ∀ t : κ, AEMeasurable (X t) Pκ := fun t =>
    (measurable_of_finite (X t)).aemeasurable
  have hprod := hIndep.charFun_map_fun_sum_eq_prod hMeas
  have hident : ∀ t : κ, IdentDistrib (X t) G Pκ Pι := by
    intro t
    simpa [X, G, Pκ, Pι] using
      (identDistrib_uniformOn_fun_eval_smul_sub_empiricalMean
        (κ := κ) (ι := ι) (E := ℝ) c Y t)
  calc
    charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
          Measure (κ → ι)).map
          (fun ωs => ∑ t : κ, c • (Y (ωs t) - empiricalMean Y)))) u =
        charFun (Pκ.map (fun ωs => ∑ t : κ, X t ωs)) u := by
          simp [Pκ, X]
    _ = (∏ t : κ, charFun (Pκ.map (X t)) u) := by
      simpa using congrFun hprod u
    _ = (∏ _t : κ, charFun (Pι.map G) u) := by
      refine Finset.prod_congr rfl ?_
      intro t _ht
      rw [(hident t).map_eq]
    _ = (charFun (Pι.map G) u) ^ Fintype.card κ := by
      simp
    _ =
      (charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι).map
          (fun i => c • (Y i - empiricalMean Y)))) u) ^ Fintype.card κ := by
      simp [Pι, G]

/-- Characteristic function of the normalized ordinary-bootstrap sample mean.

This rewrites the CLT-scaled statistic
`sqrt (#κ) * (Ybar* - Ybar)` as a sum of iid centered empirical draws scaled by
`(sqrt (#κ))⁻¹`, so the characteristic function is the centered empirical
one-draw characteristic function at the CLT scale, raised to `#κ`. -/
theorem charFun_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_pow
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (u : ℝ) :
    charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
          Measure (κ → ι)).map
          (fun ωs =>
            Real.sqrt (Fintype.card κ : ℝ) *
              (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
                empiricalMean Y)))) u =
      (charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι).map
          (fun i => Y i - empiricalMean Y)))
        ((Real.sqrt (Fintype.card κ : ℝ))⁻¹ * u)) ^ Fintype.card κ := by
  classical
  let c : ℝ := (Real.sqrt (Fintype.card κ : ℝ))⁻¹
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_ne : Real.sqrt (Fintype.card κ : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hcard_pos).ne'
  have hsqrt_sq :
      Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
    Real.sq_sqrt hcard_pos.le
  have hcoef :
      Real.sqrt (Fintype.card κ : ℝ) *
          (Fintype.card κ : ℝ)⁻¹ =
        c := by
    calc
      Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)⁻¹ =
          Real.sqrt (Fintype.card κ : ℝ) *
            (Real.sqrt (Fintype.card κ : ℝ) ^ 2)⁻¹ := by
            rw [hsqrt_sq]
      _ = (Real.sqrt (Fintype.card κ : ℝ))⁻¹ := by
            field_simp [hsqrt_ne]
      _ = c := rfl
  have hcard_coef :
      (Fintype.card κ : ℝ) * c =
        Real.sqrt (Fintype.card κ : ℝ) := by
    calc
      (Fintype.card κ : ℝ) * c =
          Real.sqrt (Fintype.card κ : ℝ) ^ 2 * c := by
            rw [hsqrt_sq]
      _ = Real.sqrt (Fintype.card κ : ℝ) := by
            rw [show c = (Real.sqrt (Fintype.card κ : ℝ))⁻¹ by rfl]
            field_simp [hsqrt_ne]
  have hstat :
      (fun ωs : κ → ι =>
        Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) =
      fun ωs : κ → ι => ∑ t : κ, c • (Y (ωs t) - empiricalMean Y) := by
    funext ωs
    change
      Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y) =
        ∑ t : κ, c * (Y (ωs t) - empiricalMean Y)
    have hcenter :
        (∑ t : κ, (Y (ωs t) - empiricalMean Y)) =
          (∑ t : κ, Y (ωs t)) - (Fintype.card κ : ℝ) * empiricalMean Y := by
      simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    calc
      Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y) =
          Real.sqrt (Fintype.card κ : ℝ) *
            ((Fintype.card κ : ℝ)⁻¹ * (∑ t : κ, Y (ωs t)) -
              empiricalMean Y) := by
            simp [empiricalBootstrapResampleMean, smul_eq_mul]
      _ = c * (∑ t : κ, Y (ωs t)) -
          Real.sqrt (Fintype.card κ : ℝ) * empiricalMean Y := by
            rw [mul_sub, ← mul_assoc, hcoef]
      _ = c * (∑ t : κ, Y (ωs t)) -
          ((Fintype.card κ : ℝ) * c) * empiricalMean Y := by
            rw [hcard_coef]
      _ = c * ((∑ t : κ, Y (ωs t)) -
          (Fintype.card κ : ℝ) * empiricalMean Y) := by
            ring
      _ = c * (∑ t : κ, (Y (ωs t) - empiricalMean Y)) := by
            rw [hcenter]
      _ = ∑ t : κ, c * (Y (ωs t) - empiricalMean Y) := by
            rw [Finset.mul_sum]
  have hpow :=
    charFun_sum_uniformOn_fun_eval_smul_sub_empiricalMean_eq_pow
      (κ := κ) (ι := ι) c Y u
  have hscale :
      charFun
          (((ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι).map
            (fun i => c • (Y i - empiricalMean Y)))) u =
        charFun
          (((ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι).map
            (fun i => Y i - empiricalMean Y))) (c * u) := by
    simpa [Pι, c, smul_eq_mul] using
      (charFun_map_mul_comp
        (μ := Pι)
        (f := fun i : ι => Y i - empiricalMean Y)
        ((measurable_of_finite (fun i : ι => Y i - empiricalMean Y)).aemeasurable)
        c u)
  calc
    charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
          Measure (κ → ι)).map
          (fun ωs =>
            Real.sqrt (Fintype.card κ : ℝ) *
              (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
                empiricalMean Y)))) u =
        charFun
          (((ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) :
            Measure (κ → ι)).map
            (fun ωs => ∑ t : κ, c • (Y (ωs t) - empiricalMean Y)))) u := by
          rw [hstat]
    _ =
      (charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι).map
          (fun i => c • (Y i - empiricalMean Y)))) u) ^ Fintype.card κ := hpow
    _ =
      (charFun
        (((ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι).map
          (fun i => Y i - empiricalMean Y)))
        ((Real.sqrt (Fintype.card κ : ℝ))⁻¹ * u)) ^ Fintype.card κ := by
        rw [hscale]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Coordinate marginal identity for finite uniform resampling.

If a bootstrap resampling point is a function `κ → ι`, drawn uniformly from
all such functions, then each coordinate has the empirical uniform law on
`ι`.  This is the finite-support marginal calculation behind Hansen's
nonparametric bootstrap equations (10.10) and (10.12). -/
theorem integral_uniformOn_fun_eval_eq_empiricalMean
    {κ : Type*} [MeasurableSpace (κ → ι)] [Finite κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) (t : κ) :
    ∫ ωs : κ → ι, Y (ωs t)
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalMean Y := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  rw [integral_uniformOn_univ_eq_card_inv_smul_sum, empiricalMean]
  have hsum :
      (∑ ωs : κ → ι, Y (ωs t)) =
        (Fintype.card ι ^ (Fintype.card κ - 1)) • ∑ i, Y i := by
    simpa [Fintype.piFinset_univ] using
      (Fintype.sum_piFinset_apply (f := Y) (s := (Finset.univ : Finset ι)) (i := t))
  rw [hsum]
  rw [← Nat.cast_smul_eq_nsmul ℝ (Fintype.card ι ^ (Fintype.card κ - 1))
      (∑ i, Y i), smul_smul]
  have hι_ne : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hκ_card : (Fintype.card κ - 1) + 1 = Fintype.card κ :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
  have hfun_card :
      (Fintype.card (κ → ι) : ℝ) =
        (Fintype.card ι : ℝ) ^ Fintype.card κ := by
    exact_mod_cast (Fintype.card_fun (α := κ) (β := ι))
  have hpow_succ :
      (Fintype.card ι : ℝ) ^ Fintype.card κ =
        (Fintype.card ι : ℝ) ^ (Fintype.card κ - 1) *
          (Fintype.card ι : ℝ) := by
    calc
      (Fintype.card ι : ℝ) ^ Fintype.card κ =
          (Fintype.card ι : ℝ) ^ ((Fintype.card κ - 1) + 1) := by
            rw [hκ_card]
      _ = (Fintype.card ι : ℝ) ^ (Fintype.card κ - 1) *
          (Fintype.card ι : ℝ) := by
            rw [pow_succ]
  have hcoeff :
      ((Fintype.card (κ → ι) : ℝ≥0∞)⁻¹).toReal *
          ((Fintype.card ι ^ (Fintype.card κ - 1) : ℕ) : ℝ) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal := by
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_pow]
    rw [hfun_card, hpow_succ]
    field_simp [hι_ne, pow_ne_zero _ hι_ne]
  rw [hcoeff]

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- If every bootstrap draw coordinate has the same conditional mean, then the
bootstrap resample mean has that conditional mean.

This is the finite-resampling linearity bridge used before specializing the
coordinate marginal law to uniform resampling from the empirical support. -/
theorem integral_empiricalBootstrapResampleMean_eq_of_coord_integrals
    {κ : Type*} [Fintype κ] [Nonempty κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ωs} {Y : ι → E} {I : Ωs → κ → ι} {m : E}
    (hInt : ∀ t, Integrable (fun ωs => Y (I ωs t)) P)
    (hcoord : ∀ t, ∫ ωs, Y (I ωs t) ∂P = m) :
    ∫ ωs, empiricalBootstrapResampleMean Y I ωs ∂P = m := by
  change ∫ ωs, ((Fintype.card κ : ℝ)⁻¹) • ∑ t, Y (I ωs t) ∂P = m
  rw [integral_smul]
  rw [integral_finset_sum]
  · simp_rw [hcoord]
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ (Fintype.card κ) m, smul_smul]
    have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [inv_mul_cancel₀ hcard_ne, one_smul]
  · intro t _ht
    exact hInt t

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Centered version of
`integral_empiricalBootstrapResampleMean_eq_of_coord_integrals`.

If every bootstrap draw coordinate has conditional mean `m`, then the resample
mean centered at `m` has conditional mean zero. -/
theorem integral_empiricalBootstrapResampleMean_sub_eq_zero_of_coord_integrals
    {κ : Type*} [Fintype κ] [Nonempty κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ωs} [IsProbabilityMeasure P]
    {Y : ι → E} {I : Ωs → κ → ι} {m : E}
    (hInt : ∀ t, Integrable (fun ωs => Y (I ωs t)) P)
    (hcoord : ∀ t, ∫ ωs, Y (I ωs t) ∂P = m) :
    ∫ ωs, empiricalBootstrapResampleMean Y I ωs - m ∂P = 0 := by
  have hmean :
      ∫ ωs, empiricalBootstrapResampleMean Y I ωs ∂P = m :=
    integral_empiricalBootstrapResampleMean_eq_of_coord_integrals
      (P := P) (Y := Y) (I := I) (m := m) hInt hcoord
  have hresampleInt :
      Integrable (fun ωs => empiricalBootstrapResampleMean Y I ωs) P := by
    change Integrable
      (fun ωs => ((Fintype.card κ : ℝ)⁻¹) • ∑ t, Y (I ωs t)) P
    exact Integrable.smul ((Fintype.card κ : ℝ)⁻¹)
      (integrable_finset_sum (s := Finset.univ)
        (f := fun t ωs => Y (I ωs t)) (fun t _ht => hInt t))
  rw [integral_sub hresampleInt (integrable_const m), hmean]
  simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Mean of the ordinary finite nonparametric bootstrap sample mean.

When the bootstrap resampling point is a function `κ → ι` drawn uniformly from
all resamples, the conditional mean of the resample mean is exactly the
finite-sample empirical mean.  This specializes the coordinate marginal law to
the textbook resample-mean object in Hansen's equations (10.10) and (10.12). -/
theorem integral_empiricalBootstrapResampleMean_uniformOn_fun_eq_empiricalMean
    {κ : Type*} [MeasurableSpace (κ → ι)] [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ ωs : κ → ι, empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalMean Y := by
  classical
  exact integral_empiricalBootstrapResampleMean_eq_of_coord_integrals
    (P := (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)))
    (Y := Y) (I := fun ωs t => ωs t) (m := empiricalMean Y)
    (fun _t => Integrable.of_finite)
    (fun t => integral_uniformOn_fun_eval_eq_empiricalMean (Y := Y) t)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Centered mean of the ordinary finite nonparametric bootstrap sample mean.

The resample mean, centered at the empirical mean, has conditional mean zero
under the finite uniform law over all resamples. -/
theorem integral_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero
    {κ : Type*} [MeasurableSpace (κ → ι)] [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ ωs : κ → ι,
        empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      0 := by
  classical
  exact integral_empiricalBootstrapResampleMean_sub_eq_zero_of_coord_integrals
    (P := (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)))
    (Y := Y) (I := fun ωs t => ωs t) (m := empiricalMean Y)
    (fun _t => Integrable.of_finite)
    (fun t => integral_uniformOn_fun_eval_eq_empiricalMean (Y := Y) t)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Normalized centered mean of the ordinary finite nonparametric-bootstrap
sample mean.

The `sqrt (#κ)` scaling used in Hansen's bootstrap CLT leaves the exact
conditional mean at zero. -/
theorem integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero
    {κ : Type*} [MeasurableSpace (κ → ι)] [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ ωs : κ → ι,
        Real.sqrt (Fintype.card κ : ℝ) •
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y)
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      0 := by
  classical
  rw [integral_smul]
  rw [integral_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero (Y := Y)]
  simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Pointwise centered-sum form of the normalized scalar ordinary-bootstrap
sample mean.

This is the finite algebra behind Hansen equation (10.14): the normalized
bootstrap mean is the sum of centered empirical draws scaled by
`1 / sqrt (#κ)`. -/
theorem normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_sum
    {κ : Type*} [Fintype κ] [Nonempty κ] (Y : ι → ℝ) (ωs : κ → ι) :
    Real.sqrt (Fintype.card κ : ℝ) *
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y) =
      (Real.sqrt (Fintype.card κ : ℝ))⁻¹ *
        ∑ t : κ, (Y (ωs t) - empiricalMean Y) := by
  classical
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsqrt_ne : Real.sqrt (Fintype.card κ : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hcard_pos).ne'
  have hsqrt_sq :
      Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
    Real.sq_sqrt hcard_pos.le
  have hcoef :
      Real.sqrt (Fintype.card κ : ℝ) *
          (Fintype.card κ : ℝ)⁻¹ =
        (Real.sqrt (Fintype.card κ : ℝ))⁻¹ := by
    calc
      Real.sqrt (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ)⁻¹ =
          Real.sqrt (Fintype.card κ : ℝ) *
            (Real.sqrt (Fintype.card κ : ℝ) ^ 2)⁻¹ := by
            rw [hsqrt_sq]
      _ = (Real.sqrt (Fintype.card κ : ℝ))⁻¹ := by
            field_simp [hsqrt_ne]
  have hsum :
      ∑ t : κ, (Y (ωs t) - empiricalMean Y) =
        ∑ t : κ, Y (ωs t) - (Fintype.card κ : ℝ) * empiricalMean Y := by
    simp [Finset.sum_sub_distrib]
  calc
    Real.sqrt (Fintype.card κ : ℝ) *
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y) =
        Real.sqrt (Fintype.card κ : ℝ) *
          ((Fintype.card κ : ℝ)⁻¹ * ∑ t : κ, Y (ωs t) - empiricalMean Y) := by
          simp [empiricalBootstrapResampleMean, smul_eq_mul]
    _ =
        (Real.sqrt (Fintype.card κ : ℝ) *
            (Fintype.card κ : ℝ)⁻¹) *
          (∑ t : κ, Y (ωs t) - (Fintype.card κ : ℝ) * empiricalMean Y) := by
          field_simp [hcard_ne]
    _ =
        (Real.sqrt (Fintype.card κ : ℝ))⁻¹ *
          ∑ t : κ, (Y (ωs t) - empiricalMean Y) := by
          rw [hcoef, hsum]

/-- Scalar finite-sample central moment, Hansen's `\hat μ_r`.

This is the one-draw empirical central moment used to state the sample
cumulants in equation (10.14). -/
noncomputable def empiricalCentralMoment (Y : ι → ℝ) (r : ℕ) : ℝ :=
  ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
    ∑ i, (Y i - empiricalMean Y) ^ r

/-- Empirical central moments are one-draw moments under the finite empirical
uniform law. -/
theorem integral_pow_sub_empiricalMean_uniformOn_univ_eq_empiricalCentralMoment
    (Y : ι → ℝ) (r : ℕ) :
    ∫ i, (Y i - empiricalMean Y) ^ r
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      empiricalCentralMoment Y r := by
  rw [integral_uniformOn_univ_eq_card_inv_smul_sum]
  rfl

/-- A single centered coordinate of the ordinary finite bootstrap resample has
the empirical central moments. -/
theorem integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
    {κ : Type*} [Finite κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (t : κ) (r : ℕ) :
    ∫ ωs : κ → ι, (Y (ωs t) - empiricalMean Y) ^ r
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalCentralMoment Y r := by
  classical
  have hident :=
    (identDistrib_uniformOn_fun_eval (κ := κ) (ι := ι) t).comp
      (measurable_of_finite (fun i : ι => (Y i - empiricalMean Y) ^ r))
  calc
    ∫ ωs : κ → ι, (Y (ωs t) - empiricalMean Y) ^ r
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        ∫ i : ι, (Y i - empiricalMean Y) ^ r
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) := by
          simpa using hident.integral_eq
    _ = empiricalCentralMoment Y r :=
          integral_pow_sub_empiricalMean_uniformOn_univ_eq_empiricalCentralMoment Y r

/-- Scalar sample cumulant `\hat κ_2`, equal to the empirical variance
normalization used in Hansen's equation (10.14). -/
noncomputable def empiricalCumulant2 (Y : ι → ℝ) : ℝ :=
  empiricalCentralMoment Y 2

/-- Scalar sample cumulant `\hat κ_3`. -/
noncomputable def empiricalCumulant3 (Y : ι → ℝ) : ℝ :=
  empiricalCentralMoment Y 3

/-- Scalar sample cumulant `\hat κ_4 = \hat μ_4 - 3 \hat κ_2^2`. -/
noncomputable def empiricalCumulant4 (Y : ι → ℝ) : ℝ :=
  empiricalCentralMoment Y 4 - 3 * empiricalCumulant2 Y ^ 2

/-- Scalar sample cumulant
`\hat κ_5 = \hat μ_5 - 10 \hat κ_3 \hat κ_2`. -/
noncomputable def empiricalCumulant5 (Y : ι → ℝ) : ℝ :=
  empiricalCentralMoment Y 5 - 10 * empiricalCumulant3 Y * empiricalCumulant2 Y

/-- Scalar sample cumulant
`\hat κ_6 = \hat μ_6 - 15\hat κ_4\hat κ_2 - 10\hat κ_3^2 -
15\hat κ_2^3`. -/
noncomputable def empiricalCumulant6 (Y : ι → ℝ) : ℝ :=
  empiricalCentralMoment Y 6 - 15 * empiricalCumulant4 Y * empiricalCumulant2 Y -
    10 * empiricalCumulant3 Y ^ 2 - 15 * empiricalCumulant2 Y ^ 3

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
@[simp]
theorem empiricalCentralMoment_three_eq_cumulant3 (Y : ι → ℝ) :
    empiricalCentralMoment Y 3 = empiricalCumulant3 Y := rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Sum over all indices except one fixed index. -/
private theorem sum_ne_eq_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a : κ) (x : ℝ) :
    (∑ b : κ, if a ≠ b then x else 0) =
      ((Fintype.card κ : ℝ) - 1) * x := by
  rw [← Finset.sum_filter]
  rw [show (Finset.univ.filter fun b : κ => a ≠ b) = Finset.univ.erase a by
    ext b
    simp [eq_comm]]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a)]
  rw [nsmul_eq_mul]
  change ((Fintype.card κ - 1 : ℕ) : ℝ) * x =
    ((Fintype.card κ : ℝ) - 1) * x
  have hcard_one : 1 ≤ Fintype.card κ :=
    Nat.succ_le_of_lt Fintype.card_pos
  rw [Nat.cast_sub hcard_one]
  norm_num

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Sum over all elements of a finite set except one fixed member. -/
private theorem sum_finset_ne_eq_card_sub_one_mul
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (a : κ) (ha : a ∈ s) (x : ℝ) :
    (∑ b ∈ s, if a ≠ b then x else 0) =
      ((s.card : ℝ) - 1) * x := by
  rw [← Finset.sum_filter]
  rw [show (s.filter fun b : κ => a ≠ b) = s.erase a by
    ext b
    by_cases hba : b = a
    · simp [hba]
    · have hab : a ≠ b := fun h => hba h.symm
      simp [hba, hab]]
  rw [Finset.sum_const, Finset.card_erase_of_mem ha]
  rw [nsmul_eq_mul]
  change ((s.card - 1 : ℕ) : ℝ) * x = ((s.card : ℝ) - 1) * x
  have hcard_one : 1 ≤ s.card := Finset.card_pos.mpr ⟨a, ha⟩
  rw [Nat.cast_sub hcard_one]
  norm_num

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the all-equal pattern in an ordered quadruple over a finite set. -/
private theorem sum_finset_allEqual4_eq_card_mul
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (x : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      if a = b ∧ a = c ∧ a = d then x else 0) =
      (s.card : ℝ) * x := by
  have hinner : ∀ a ∈ s,
      (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        if a = b ∧ a = c ∧ a = d then x else 0) = x := by
    intro a ha
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro d hd hda
          have had : a ≠ d := fun h => hda h.symm
          simp [had]
        · intro hdnone
          exact (hdnone ha).elim
      · intro c hc hca
        have hac : a ≠ c := fun h => hca h.symm
        simp [hac]
      · intro hcnone
        exact (hcnone ha).elim
    · intro b hb hba
      have hab : a ≠ b := fun h => hba h.symm
      simp [hab]
    · intro hbnone
      exact (hbnone ha).elim
  calc
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        if a = b ∧ a = c ∧ a = d then x else 0) =
        ∑ _a ∈ s, x := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hinner a ha
    _ = (s.card : ℝ) * x := by
          simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count one ordered two-pair partition in a quadruple over a finite set. -/
private theorem sum_finset_pairPattern_eq_card_mul_card_sub_one_mul
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (x : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      if a = b ∧ c = d ∧ a ≠ c then x else 0) =
      (s.card : ℝ) * ((s.card : ℝ) - 1) * x := by
  have hinner : ∀ a ∈ s,
      (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        if a = b ∧ c = d ∧ a ≠ c then x else 0) =
        ((s.card : ℝ) - 1) * x := by
    intro a ha
    rw [Finset.sum_eq_single a]
    · have hc :
        (∑ c ∈ s, ∑ d ∈ s, if a = a ∧ c = d ∧ a ≠ c then x else 0) =
          ∑ c ∈ s, if a ≠ c then x else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.sum_eq_single c]
        · by_cases hac : a ≠ c <;> simp [hac]
        · intro d hd hdc
          have hcd : c ≠ d := fun h => hdc h.symm
          simp [hcd]
        · intro hcnone
          exact (hcnone hc).elim
      rw [hc]
      exact sum_finset_ne_eq_card_sub_one_mul s a ha x
    · intro b hb hba
      have hab : a ≠ b := fun h => hba h.symm
      simp [hab]
    · intro hanone
      exact (hanone ha).elim
  calc
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        if a = b ∧ c = d ∧ a ≠ c then x else 0) =
        ∑ a ∈ s, ((s.card : ℝ) - 1) * x := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hinner a ha
    _ = (s.card : ℝ) * ((s.card : ℝ) - 1) * x := by
          simp [mul_assoc]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `a = c`, `b = d` pair partition over a finite set. -/
private theorem sum_finset_pairPattern_ac_bd_eq_card_mul_card_sub_one_mul
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (x : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      if a = c ∧ b = d ∧ a ≠ b then x else 0) =
      (s.card : ℝ) * ((s.card : ℝ) - 1) * x := by
  calc
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        if a = c ∧ b = d ∧ a ≠ b then x else 0) =
        ∑ a ∈ s, ∑ c ∈ s, ∑ b ∈ s, ∑ d ∈ s,
          if a = c ∧ b = d ∧ a ≠ b then x else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
    _ = (s.card : ℝ) * ((s.card : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_finset_pairPattern_eq_card_mul_card_sub_one_mul s x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `a = d`, `b = c` pair partition over a finite set. -/
private theorem sum_finset_pairPattern_ad_bc_eq_card_mul_card_sub_one_mul
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (x : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      if a = d ∧ b = c ∧ a ≠ b then x else 0) =
      (s.card : ℝ) * ((s.card : ℝ) - 1) * x := by
  calc
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        if a = d ∧ b = c ∧ a ≠ b then x else 0) =
        ∑ a ∈ s, ∑ d ∈ s, ∑ b ∈ s, ∑ c ∈ s,
          if a = d ∧ b = c ∧ a ≠ b then x else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          calc
            (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
                if a = d ∧ b = c ∧ a ≠ b then x else 0) =
                ∑ b ∈ s, ∑ d ∈ s, ∑ c ∈ s,
                  if a = d ∧ b = c ∧ a ≠ b then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  rw [Finset.sum_comm]
            _ = ∑ d ∈ s, ∑ b ∈ s, ∑ c ∈ s,
                  if a = d ∧ b = c ∧ a ≠ b then x else 0 := by
                  rw [Finset.sum_comm]
    _ = (s.card : ℝ) * ((s.card : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_finset_pairPattern_eq_card_mul_card_sub_one_mul s x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count one ordered pair partition in a quadruple index sum. -/
private theorem sum_pairPattern_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
      if a = b ∧ c = d ∧ a ≠ c then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  have hneqsum : ∀ a : κ,
      (∑ c : κ, if a ≠ c then x else 0) =
        ((Fintype.card κ : ℝ) - 1) * x := fun a =>
    sum_ne_eq_card_sub_one_mul a x
  have hinner : ∀ a : κ,
      (∑ b : κ, ∑ c : κ, ∑ d : κ,
        if a = b ∧ c = d ∧ a ≠ c then x else 0) =
        ((Fintype.card κ : ℝ) - 1) * x := by
    intro a
    rw [Finset.sum_eq_single a]
    · have hc :
        (∑ c : κ, ∑ d : κ, if a = a ∧ c = d ∧ a ≠ c then x else 0) =
          (∑ c : κ, if a ≠ c then x else 0) := by
        congr with c
        rw [Finset.sum_eq_single c]
        · by_cases hac : a ≠ c <;> simp [hac]
        · intro d _hd_mem hd
          have hcd : c ≠ d := fun h => hd h.symm
          simp [hcd]
        · intro hcnot
          exact (hcnot (Finset.mem_univ c)).elim
      rw [hc, hneqsum a]
    · intro b _hb_mem hb
      have hab : a ≠ b := fun h => hb h.symm
      simp [hab]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
        if a = b ∧ c = d ∧ a ≠ c then x else 0) =
        ∑ a : κ, ((Fintype.card κ : ℝ) - 1) * x := by
          simp [hinner]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simp [mul_assoc]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `a = c`, `b = d` ordered pair partition. -/
private theorem sum_pairPattern_ac_bd_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
      if a = c ∧ b = d ∧ a ≠ b then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  have hinner : ∀ a : κ,
      (∑ b : κ, ∑ c : κ, ∑ d : κ,
        if a = c ∧ b = d ∧ a ≠ b then x else 0) =
        ((Fintype.card κ : ℝ) - 1) * x := by
    intro a
    have hb : ∀ b : κ,
        (∑ c : κ, ∑ d : κ, if a = c ∧ b = d ∧ a ≠ b then x else 0) =
          if a ≠ b then x else 0 := by
      intro b
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · by_cases hab : a ≠ b <;> simp [hab]
        · intro d _hd_mem hd
          have hbd : b ≠ d := fun h => hd h.symm
          simp [hbd]
        · intro hdnone
          exact (hdnone (Finset.mem_univ b)).elim
      · intro c _hc_mem hc
        have hac : a ≠ c := fun h => hc h.symm
        simp [hac]
      · intro hcnone
        exact (hcnone (Finset.mem_univ a)).elim
    calc
      (∑ b : κ, ∑ c : κ, ∑ d : κ,
          if a = c ∧ b = d ∧ a ≠ b then x else 0) =
          ∑ b : κ, if a ≠ b then x else 0 := by
            simp [hb]
      _ = ((Fintype.card κ : ℝ) - 1) * x :=
          sum_ne_eq_card_sub_one_mul a x
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
        if a = c ∧ b = d ∧ a ≠ b then x else 0) =
        ∑ a : κ, ((Fintype.card κ : ℝ) - 1) * x := by
          simp [hinner]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simp [mul_assoc]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `a = d`, `b = c` ordered pair partition. -/
private theorem sum_pairPattern_ad_bc_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
      if a = d ∧ b = c ∧ a ≠ b then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  have hinner : ∀ a : κ,
      (∑ b : κ, ∑ c : κ, ∑ d : κ,
        if a = d ∧ b = c ∧ a ≠ b then x else 0) =
        ((Fintype.card κ : ℝ) - 1) * x := by
    intro a
    have hb : ∀ b : κ,
        (∑ c : κ, ∑ d : κ, if a = d ∧ b = c ∧ a ≠ b then x else 0) =
          if a ≠ b then x else 0 := by
      intro b
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · by_cases hab : a ≠ b <;> simp [hab]
        · intro d _hd_mem hd
          have had : a ≠ d := fun h => hd h.symm
          simp [had]
        · intro hdnone
          exact (hdnone (Finset.mem_univ a)).elim
      · intro c _hc_mem hc
        have hbc : b ≠ c := fun h => hc h.symm
        simp [hbc]
      · intro hcnone
        exact (hcnone (Finset.mem_univ b)).elim
    calc
      (∑ b : κ, ∑ c : κ, ∑ d : κ,
          if a = d ∧ b = c ∧ a ≠ b then x else 0) =
          ∑ b : κ, if a ≠ b then x else 0 := by
            simp [hb]
      _ = ((Fintype.card κ : ℝ) - 1) * x :=
          sum_ne_eq_card_sub_one_mul a x
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
        if a = d ∧ b = c ∧ a ≠ b then x else 0) =
        ∑ a : κ, ((Fintype.card κ : ℝ) - 1) * x := by
          simp [hinner]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simp [mul_assoc]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the all-equal pattern in an ordered quadruple index sum. -/
private theorem sum_allEqual4_eq_card_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
      if a = b ∧ a = c ∧ a = d then x else 0) =
      (Fintype.card κ : ℝ) * x := by
  have hinner : ∀ a : κ,
      (∑ b : κ, ∑ c : κ, ∑ d : κ,
        if a = b ∧ a = c ∧ a = d then x else 0) = x := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro d _hd_mem hd
          have had : a ≠ d := fun h => hd h.symm
          simp [had]
        · intro hdnone
          exact (hdnone (Finset.mem_univ a)).elim
      · intro c _hc_mem hc
        have hac : a ≠ c := fun h => hc h.symm
        simp [hac]
      · intro hcnone
        exact (hcnone (Finset.mem_univ a)).elim
    · intro b _hb_mem hb
      have hab : a ≠ b := fun h => hb h.symm
      simp [hab]
    · intro hbnone
      exact (hbnone (Finset.mem_univ a)).elim
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
        if a = b ∧ a = c ∧ a = d then x else 0) =
        ∑ _a : κ, x := by
          simp [hinner]
    _ = (Fintype.card κ : ℝ) * x := by
          simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the all-equal pattern in an ordered quintuple index sum. -/
private theorem sum_allEqual5_eq_card_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if a = b ∧ a = c ∧ a = d ∧ a = e then x else 0) =
      (Fintype.card κ : ℝ) * x := by
  have hinner : ∀ a : κ,
      (∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = b ∧ a = c ∧ a = d ∧ a = e then x else 0) = x := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single a]
          · simp
          · intro e _he_mem he
            have hae : a ≠ e := fun h => he h.symm
            simp [hae]
          · intro henone
            exact (henone (Finset.mem_univ a)).elim
        · intro d _hd_mem hd
          have had : a ≠ d := fun h => hd h.symm
          simp [had]
        · intro hdnone
          exact (hdnone (Finset.mem_univ a)).elim
      · intro c _hc_mem hc
        have hac : a ≠ c := fun h => hc h.symm
        simp [hac]
      · intro hcnone
        exact (hcnone (Finset.mem_univ a)).elim
    · intro b _hb_mem hb
      have hab : a ≠ b := fun h => hb h.symm
      simp [hab]
    · intro hbnone
      exact (hbnone (Finset.mem_univ a)).elim
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = b ∧ a = c ∧ a = d ∧ a = e then x else 0) =
        ∑ _a : κ, x := by
          simp [hinner]
    _ = (Fintype.card κ : ℝ) * x := by
          simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `abc/de` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if a = b ∧ a = c ∧ d = e ∧ a ≠ d then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  have hinner : ∀ a : κ,
      (∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = b ∧ a = c ∧ d = e ∧ a ≠ d then x else 0) =
        ((Fintype.card κ : ℝ) - 1) * x := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · have hd : ∀ d : κ,
            (∑ e : κ, if a = a ∧ a = a ∧ d = e ∧ a ≠ d then x else 0) =
              if a ≠ d then x else 0 := by
          intro d
          rw [Finset.sum_eq_single d]
          · by_cases had : a ≠ d <;> simp [had]
          · intro e _he_mem he
            have hde : d ≠ e := fun h => he h.symm
            simp [hde]
          · intro hdnone
            exact (hdnone (Finset.mem_univ d)).elim
        calc
          (∑ d : κ, ∑ e : κ, if a = a ∧ a = a ∧ d = e ∧ a ≠ d then x else 0) =
              ∑ d : κ, if a ≠ d then x else 0 := by
                congr with d
                exact hd d
          _ = ((Fintype.card κ : ℝ) - 1) * x :=
              sum_ne_eq_card_sub_one_mul a x
      · intro c _hc_mem hc
        have hac : a ≠ c := fun h => hc h.symm
        simp [hac]
      · intro hcnone
        exact (hcnone (Finset.mem_univ a)).elim
    · intro b _hb_mem hb
      have hab : a ≠ b := fun h => hb h.symm
      simp [hab]
    · intro hbnone
      exact (hbnone (Finset.mem_univ a)).elim
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = b ∧ a = c ∧ d = e ∧ a ≠ d then x else 0) =
        ∑ a : κ, ((Fintype.card κ : ℝ) - 1) * x := by
          simp [hinner]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simp [mul_assoc]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `abd/ce` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_abd_ce_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if a = b ∧ a = d ∧ c = e ∧ a ≠ c then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = b ∧ a = d ∧ c = e ∧ a ≠ c then x else 0) =
        ∑ a : κ, ∑ b : κ, ∑ d : κ, ∑ c : κ, ∑ e : κ,
          if a = b ∧ a = d ∧ c = e ∧ a ≠ c then x else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          apply Finset.sum_congr rfl
          intro b _hb
          rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `abe/cd` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_abe_cd_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if a = b ∧ a = e ∧ c = d ∧ a ≠ c then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = b ∧ a = e ∧ c = d ∧ a ≠ c then x else 0) =
        ∑ a : κ, ∑ b : κ, ∑ e : κ, ∑ c : κ, ∑ d : κ,
          if a = b ∧ a = e ∧ c = d ∧ a ≠ c then x else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          apply Finset.sum_congr rfl
          intro b _hb
          calc
            (∑ c : κ, ∑ d : κ, ∑ e : κ,
                if a = b ∧ a = e ∧ c = d ∧ a ≠ c then x else 0) =
                ∑ c : κ, ∑ e : κ, ∑ d : κ,
                  if a = b ∧ a = e ∧ c = d ∧ a ≠ c then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro c _hc
                  rw [Finset.sum_comm]
            _ = ∑ e : κ, ∑ c : κ, ∑ d : κ,
                  if a = b ∧ a = e ∧ c = d ∧ a ≠ c then x else 0 := by
                  rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `acd/be` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_acd_be_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if a = c ∧ a = d ∧ b = e ∧ a ≠ b then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = c ∧ a = d ∧ b = e ∧ a ≠ b then x else 0) =
        ∑ a : κ, ∑ c : κ, ∑ d : κ, ∑ b : κ, ∑ e : κ,
          if a = c ∧ a = d ∧ b = e ∧ a ≠ b then x else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          calc
            (∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                if a = c ∧ a = d ∧ b = e ∧ a ≠ b then x else 0) =
                ∑ c : κ, ∑ b : κ, ∑ d : κ, ∑ e : κ,
                  if a = c ∧ a = d ∧ b = e ∧ a ≠ b then x else 0 := by
                  rw [Finset.sum_comm]
            _ = ∑ c : κ, ∑ d : κ, ∑ b : κ, ∑ e : κ,
                  if a = c ∧ a = d ∧ b = e ∧ a ≠ b then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro c _hc
                  rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `ace/bd` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_ace_bd_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0) =
        ∑ a : κ, ∑ c : κ, ∑ e : κ, ∑ b : κ, ∑ d : κ,
          if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          calc
            (∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0) =
                ∑ c : κ, ∑ b : κ, ∑ d : κ, ∑ e : κ,
                  if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0 := by
                  rw [Finset.sum_comm]
            _ = ∑ c : κ, ∑ e : κ, ∑ b : κ, ∑ d : κ,
                  if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro c _hc
                  calc
                    (∑ b : κ, ∑ d : κ, ∑ e : κ,
                        if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0) =
                        ∑ b : κ, ∑ e : κ, ∑ d : κ,
                          if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0 := by
                          apply Finset.sum_congr rfl
                          intro b _hb
                          rw [Finset.sum_comm]
                    _ = ∑ e : κ, ∑ b : κ, ∑ d : κ,
                          if a = c ∧ a = e ∧ b = d ∧ a ≠ b then x else 0 := by
                          rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `ade/bc` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_ade_bc_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if a = d ∧ a = e ∧ b = c ∧ a ≠ b then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if a = d ∧ a = e ∧ b = c ∧ a ≠ b then x else 0) =
        ∑ a : κ, ∑ d : κ, ∑ e : κ, ∑ b : κ, ∑ c : κ,
          if a = d ∧ a = e ∧ b = c ∧ a ≠ b then x else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          calc
            (∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                if a = d ∧ a = e ∧ b = c ∧ a ≠ b then x else 0) =
                ∑ b : κ, ∑ d : κ, ∑ c : κ, ∑ e : κ,
                  if a = d ∧ a = e ∧ b = c ∧ a ≠ b then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro b _hb
                  rw [Finset.sum_comm]
            _ = ∑ d : κ, ∑ b : κ, ∑ c : κ, ∑ e : κ,
                  if a = d ∧ a = e ∧ b = c ∧ a ≠ b then x else 0 := by
                  rw [Finset.sum_comm]
            _ = ∑ d : κ, ∑ b : κ, ∑ e : κ, ∑ c : κ,
                  if a = d ∧ a = e ∧ b = c ∧ a ≠ b then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro d _hd
                  apply Finset.sum_congr rfl
                  intro b _hb
                  rw [Finset.sum_comm]
            _ = ∑ d : κ, ∑ e : κ, ∑ b : κ, ∑ c : κ,
                  if a = d ∧ a = e ∧ b = c ∧ a ≠ b then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro d _hd
                  rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `bcd/ae` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_bcd_ae_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if b = c ∧ b = d ∧ a = e ∧ b ≠ a then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if b = c ∧ b = d ∧ a = e ∧ b ≠ a then x else 0) =
        ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ a : κ, ∑ e : κ,
          if b = c ∧ b = d ∧ a = e ∧ b ≠ a then x else 0 := by
          calc
            (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                if b = c ∧ b = d ∧ a = e ∧ b ≠ a then x else 0) =
                ∑ b : κ, ∑ a : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                  if b = c ∧ b = d ∧ a = e ∧ b ≠ a then x else 0 := by
                  rw [Finset.sum_comm]
            _ = ∑ b : κ, ∑ c : κ, ∑ a : κ, ∑ d : κ, ∑ e : κ,
                  if b = c ∧ b = d ∧ a = e ∧ b ≠ a then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro b _hb
                  rw [Finset.sum_comm]
            _ = ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ a : κ, ∑ e : κ,
                  if b = c ∧ b = d ∧ a = e ∧ b ≠ a then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro b _hb
                  apply Finset.sum_congr rfl
                  intro c _hc
                  rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `bce/ad` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_bce_ad_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if b = c ∧ b = e ∧ a = d ∧ b ≠ a then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if b = c ∧ b = e ∧ a = d ∧ b ≠ a then x else 0) =
        ∑ b : κ, ∑ c : κ, ∑ e : κ, ∑ a : κ, ∑ d : κ,
          if b = c ∧ b = e ∧ a = d ∧ b ≠ a then x else 0 := by
          calc
            (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                if b = c ∧ b = e ∧ a = d ∧ b ≠ a then x else 0) =
                ∑ b : κ, ∑ a : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                  if b = c ∧ b = e ∧ a = d ∧ b ≠ a then x else 0 := by
                  rw [Finset.sum_comm]
            _ = ∑ b : κ, ∑ c : κ, ∑ a : κ, ∑ d : κ, ∑ e : κ,
                  if b = c ∧ b = e ∧ a = d ∧ b ≠ a then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro b _hb
                  rw [Finset.sum_comm]
            _ = ∑ b : κ, ∑ c : κ, ∑ a : κ, ∑ e : κ, ∑ d : κ,
                  if b = c ∧ b = e ∧ a = d ∧ b ≠ a then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro b _hb
                  apply Finset.sum_congr rfl
                  intro c _hc
                  apply Finset.sum_congr rfl
                  intro a _ha
                  rw [Finset.sum_comm]
            _ = ∑ b : κ, ∑ c : κ, ∑ e : κ, ∑ a : κ, ∑ d : κ,
                  if b = c ∧ b = e ∧ a = d ∧ b ≠ a then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro b _hb
                  apply Finset.sum_congr rfl
                  intro c _hc
                  rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `bde/ac` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_bde_ac_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0) =
        ∑ b : κ, ∑ d : κ, ∑ e : κ, ∑ a : κ, ∑ c : κ,
          if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0 := by
          calc
            (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0) =
                ∑ b : κ, ∑ a : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                  if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0 := by
                  rw [Finset.sum_comm]
            _ = ∑ b : κ, ∑ d : κ, ∑ e : κ, ∑ a : κ, ∑ c : κ,
                  if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro b _hb
                  calc
                    (∑ a : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                        if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0) =
                        ∑ a : κ, ∑ d : κ, ∑ c : κ, ∑ e : κ,
                          if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0 := by
                          apply Finset.sum_congr rfl
                          intro a _ha
                          rw [Finset.sum_comm]
                    _ = ∑ d : κ, ∑ a : κ, ∑ c : κ, ∑ e : κ,
                          if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0 := by
                          rw [Finset.sum_comm]
                    _ = ∑ d : κ, ∑ a : κ, ∑ e : κ, ∑ c : κ,
                          if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0 := by
                          apply Finset.sum_congr rfl
                          intro d _hd
                          apply Finset.sum_congr rfl
                          intro a _ha
                          rw [Finset.sum_comm]
                    _ = ∑ d : κ, ∑ e : κ, ∑ a : κ, ∑ c : κ,
                          if b = d ∧ b = e ∧ a = c ∧ b ≠ a then x else 0 := by
                          apply Finset.sum_congr rfl
                          intro d _hd
                          rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Count the `cde/ab` ordered triple-pair partition in a quintuple sum. -/
private theorem sum_triplePairPattern_cde_ab_eq_card_mul_card_sub_one_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (x : ℝ) :
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
      if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0) =
      (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
  calc
    (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
        if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0) =
        ∑ c : κ, ∑ d : κ, ∑ e : κ, ∑ a : κ, ∑ b : κ,
          if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0 := by
          calc
            (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
                if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0) =
                ∑ a : κ, ∑ c : κ, ∑ b : κ, ∑ d : κ, ∑ e : κ,
                  if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro a _ha
                  rw [Finset.sum_comm]
            _ = ∑ c : κ, ∑ a : κ, ∑ b : κ, ∑ d : κ, ∑ e : κ,
                  if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0 := by
                  rw [Finset.sum_comm]
            _ = ∑ c : κ, ∑ d : κ, ∑ e : κ, ∑ a : κ, ∑ b : κ,
                  if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0 := by
                  apply Finset.sum_congr rfl
                  intro c _hc
                  calc
                    (∑ a : κ, ∑ b : κ, ∑ d : κ, ∑ e : κ,
                        if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0) =
                        ∑ a : κ, ∑ d : κ, ∑ b : κ, ∑ e : κ,
                          if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0 := by
                          apply Finset.sum_congr rfl
                          intro a _ha
                          rw [Finset.sum_comm]
                    _ = ∑ d : κ, ∑ a : κ, ∑ b : κ, ∑ e : κ,
                          if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0 := by
                          rw [Finset.sum_comm]
                    _ = ∑ d : κ, ∑ a : κ, ∑ e : κ, ∑ b : κ,
                          if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0 := by
                          apply Finset.sum_congr rfl
                          intro d _hd
                          apply Finset.sum_congr rfl
                          intro a _ha
                          rw [Finset.sum_comm]
                    _ = ∑ d : κ, ∑ e : κ, ∑ a : κ, ∑ b : κ,
                          if c = d ∧ c = e ∧ a = b ∧ c ≠ a then x else 0 := by
                          apply Finset.sum_congr rfl
                          intro d _hd
                          rw [Finset.sum_comm]
    _ = (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * x := by
          simpa [and_assoc] using
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul (κ := κ) x

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- If a quadruple is neither all equal nor one of the three ordered
two-pair patterns, then at least one coordinate appears as a singleton. -/
private theorem exists_singleton_of_not_allEqual4_not_pairPatterns
    {κ : Type*} {a b c d : κ}
    (hAll : ¬ (a = b ∧ a = c ∧ a = d))
    (hABCD : ¬ (a = b ∧ c = d ∧ a ≠ c))
    (hACBD : ¬ (a = c ∧ b = d ∧ a ≠ b))
    (hADBC : ¬ (a = d ∧ b = c ∧ a ≠ b)) :
    (a ≠ b ∧ a ≠ c ∧ a ≠ d) ∨
      (b ≠ a ∧ b ≠ c ∧ b ≠ d) ∨
        (c ≠ a ∧ c ≠ b ∧ c ≠ d) ∨
          (d ≠ a ∧ d ≠ b ∧ d ≠ c) := by
  classical
  by_cases hab : a = b <;>
    by_cases hac : a = c <;>
    by_cases had : a = d <;>
    by_cases hbc : b = c <;>
    by_cases hbd : b = d <;>
    by_cases hcd : c = d <;>
    simp_all [eq_comm]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- If a quintuple is neither all equal nor one of the ordered triple-pair
patterns, then at least one coordinate appears as a singleton. -/
private theorem exists_singleton_of_not_allEqual5_not_triplePairPatterns
    {κ : Type*} {a b c d e : κ}
    (hAll : ¬ (a = b ∧ a = c ∧ a = d ∧ a = e))
    (hABC_DE : ¬ (a = b ∧ a = c ∧ d = e ∧ a ≠ d))
    (hABD_CE : ¬ (a = b ∧ a = d ∧ c = e ∧ a ≠ c))
    (hABE_CD : ¬ (a = b ∧ a = e ∧ c = d ∧ a ≠ c))
    (hACD_BE : ¬ (a = c ∧ a = d ∧ b = e ∧ a ≠ b))
    (hACE_BD : ¬ (a = c ∧ a = e ∧ b = d ∧ a ≠ b))
    (hADE_BC : ¬ (a = d ∧ a = e ∧ b = c ∧ a ≠ b))
    (hBCD_AE : ¬ (b = c ∧ b = d ∧ a = e ∧ b ≠ a))
    (hBCE_AD : ¬ (b = c ∧ b = e ∧ a = d ∧ b ≠ a))
    (hBDE_AC : ¬ (b = d ∧ b = e ∧ a = c ∧ b ≠ a))
    (hCDE_AB : ¬ (c = d ∧ c = e ∧ a = b ∧ c ≠ a)) :
    (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e) ∨
      (b ≠ a ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e) ∨
        (c ≠ a ∧ c ≠ b ∧ c ≠ d ∧ c ≠ e) ∨
          (d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ d ≠ e) ∨
            (e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d) := by
  classical
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c <;>
      by_cases had : a = d <;>
      by_cases hae : a = e <;>
      by_cases hcd : c = d <;>
      by_cases hce : c = e <;>
      by_cases hde : d = e <;>
      simp_all [eq_comm]
  · by_cases hac : a = c
    · subst c
      by_cases had : a = d <;>
        by_cases hae : a = e <;>
        by_cases hbd : b = d <;>
        by_cases hbe : b = e <;>
        by_cases hde : d = e <;>
        simp_all [eq_comm]
    · by_cases had : a = d
      · subst d
        by_cases hae : a = e <;>
          by_cases hbc : b = c <;>
          by_cases hbe : b = e <;>
          by_cases hce : c = e <;>
          simp_all [eq_comm]
      · by_cases hae : a = e
        · subst e
          by_cases hbc : b = c <;>
            by_cases hbd : b = d <;>
            by_cases hcd : c = d <;>
            simp_all [eq_comm]
        · exact Or.inl ⟨hab, hac, had, hae⟩

/-- Product of two centered ordinary-bootstrap coordinates.

Distinct coordinates factor into centered one-draw means and vanish; equal
coordinates give the empirical second cumulant. -/
theorem integral_mul_uniformOn_fun_eval_sub_empiricalMean_eq
    {κ : Type*} [Finite κ] [DecidableEq κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (a b : κ) :
    ∫ ωs : κ → ι,
        (Y (ωs a) - empiricalMean Y) *
          (Y (ωs b) - empiricalMean Y)
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      if a = b then empiricalCumulant2 Y else 0 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  have hIndep : iIndepFun X Pκ := by
    simpa [X, Pκ] using
      (iIndepFun_uniformOn_fun_eval_sub_empiricalMean
        (κ := κ) (ι := ι) (E := ℝ) Y)
  have hMeas : ∀ t : κ, Measurable (X t) := fun t =>
    measurable_of_finite (X t)
  have hAEStrong : ∀ t : κ, AEStronglyMeasurable (X t) Pκ := fun t =>
    (hMeas t).aestronglyMeasurable
  have hmean : ∀ t : κ, ∫ ωs, X t ωs ∂Pκ = 0 := by
    intro t
    have hbase :
        ∫ ωs : κ → ι, Y (ωs t) ∂Pκ = empiricalMean Y := by
      simpa [Pκ] using
        (integral_uniformOn_fun_eval_eq_empiricalMean
          (κ := κ) (Y := Y) t)
    have hInt : Integrable (fun ωs : κ → ι => Y (ωs t)) Pκ :=
      Integrable.of_finite
    calc
      ∫ ωs, X t ωs ∂Pκ =
          ∫ ωs : κ → ι, Y (ωs t) - empiricalMean Y ∂Pκ := rfl
      _ = ∫ ωs : κ → ι, Y (ωs t) ∂Pκ - ∫ _ωs : κ → ι, empiricalMean Y ∂Pκ := by
          rw [integral_sub hInt (integrable_const _)]
      _ = 0 := by
          rw [hbase]
          simp [Pκ]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    change ∫ ωs, X a ωs * X a ωs ∂Pκ = empiricalCumulant2 Y
    calc
      ∫ ωs, X a ωs * X a ωs ∂Pκ =
          ∫ ωs, X a ωs ^ 2 ∂Pκ := by
            congr with ωs
            ring
      _ = empiricalCumulant2 Y := by
          change
            ∫ ωs : κ → ι, (Y (ωs a) - empiricalMean Y) ^ 2
                ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
              empiricalCumulant2 Y
          exact
            integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
              (κ := κ) (Y := Y) a 2
  · rw [if_neg hab]
    have hmul :
        ∫ ωs, X a ωs * X b ωs ∂Pκ =
          (∫ ωs, X a ωs ∂Pκ) * ∫ ωs, X b ωs ∂Pκ :=
      (hIndep.indepFun hab).integral_mul_eq_mul_integral
        (hAEStrong a) (hAEStrong b)
    calc
      ∫ ωs : κ → ι, (Y (ωs a) - empiricalMean Y) *
          (Y (ωs b) - empiricalMean Y) ∂Pκ =
          ∫ ωs, X a ωs * X b ωs ∂Pκ := rfl
      _ = (∫ ωs, X a ωs ∂Pκ) * ∫ ωs, X b ωs ∂Pκ := hmul
      _ = 0 := by rw [hmean a, zero_mul]

/-- Triple product of centered ordinary-bootstrap coordinates.

For three centered resampled observations, the only nonzero conditional
third-moment term is the all-equal index case. -/
theorem integral_mul_mul_uniformOn_fun_eval_sub_empiricalMean_eq
    {κ : Type*} [Finite κ] [DecidableEq κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (a b c : κ) :
    ∫ ωs : κ → ι,
        (Y (ωs a) - empiricalMean Y) *
          (Y (ωs b) - empiricalMean Y) *
          (Y (ωs c) - empiricalMean Y)
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      if a = b ∧ a = c then empiricalCumulant3 Y else 0 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  have hIndep : iIndepFun X Pκ := by
    simpa [X, Pκ] using
      (iIndepFun_uniformOn_fun_eval_sub_empiricalMean
        (κ := κ) (ι := ι) (E := ℝ) Y)
  have hMeas : ∀ t : κ, Measurable (X t) := fun t =>
    measurable_of_finite (X t)
  have hAEStrong : ∀ t : κ, AEStronglyMeasurable (X t) Pκ := fun t =>
    (hMeas t).aestronglyMeasurable
  have hmean : ∀ t : κ, ∫ ωs, X t ωs ∂Pκ = 0 := by
    intro t
    have hbase :
        ∫ ωs : κ → ι, Y (ωs t) ∂Pκ = empiricalMean Y := by
      simpa [Pκ] using
        (integral_uniformOn_fun_eval_eq_empiricalMean
          (κ := κ) (Y := Y) t)
    have hInt : Integrable (fun ωs : κ → ι => Y (ωs t)) Pκ :=
      Integrable.of_finite
    calc
      ∫ ωs, X t ωs ∂Pκ =
          ∫ ωs : κ → ι, Y (ωs t) - empiricalMean Y ∂Pκ := rfl
      _ = ∫ ωs : κ → ι, Y (ωs t) ∂Pκ - ∫ _ωs : κ → ι, empiricalMean Y ∂Pκ := by
          rw [integral_sub hInt (integrable_const _)]
      _ = 0 := by
          rw [hbase]
          simp [Pκ]
  have hthird : ∀ t : κ, ∫ ωs, X t ωs ^ 3 ∂Pκ = empiricalCumulant3 Y := by
    intro t
    change
      ∫ ωs : κ → ι, (Y (ωs t) - empiricalMean Y) ^ 3
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        empiricalCumulant3 Y
    rw [← empiricalCentralMoment_three_eq_cumulant3 Y]
    exact
      (integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) t 3)
  by_cases hab : a = b
  · by_cases hac : a = c
    · subst b
      subst c
      rw [if_pos ⟨rfl, rfl⟩]
      change ∫ ωs, X a ωs * X a ωs * X a ωs ∂Pκ = empiricalCumulant3 Y
      calc
        ∫ ωs, X a ωs * X a ωs * X a ωs ∂Pκ =
            ∫ ωs, X a ωs ^ 3 ∂Pκ := by
              congr with ωs
              ring
        _ = empiricalCumulant3 Y := hthird a
    · have hbc : b ≠ c := by
        simpa [hab] using hac
      have hmul :
          ∫ ωs, (X a * X b) ωs * X c ωs ∂Pκ =
            (∫ ωs, (X a * X b) ωs ∂Pκ) * ∫ ωs, X c ωs ∂Pκ :=
        (hIndep.indepFun_mul_left hMeas a b c hac hbc).integral_mul_eq_mul_integral
          ((hAEStrong a).mul (hAEStrong b)) (hAEStrong c)
      have hz :
          ∫ ωs, X a ωs * X b ωs * X c ωs ∂Pκ = 0 := by
        calc
          ∫ ωs, X a ωs * X b ωs * X c ωs ∂Pκ =
              ∫ ωs, (X a * X b) ωs * X c ωs ∂Pκ := rfl
          _ = (∫ ωs, (X a * X b) ωs ∂Pκ) * ∫ ωs, X c ωs ∂Pκ := hmul
          _ = 0 := by rw [hmean c, mul_zero]
      rw [if_neg (by intro h; exact hac h.2)]
      simpa [X, Pκ] using hz
  · by_cases hac : a = c
    · subst c
      have hmul :
          ∫ ωs, (X a * X a) ωs * X b ωs ∂Pκ =
            (∫ ωs, (X a * X a) ωs ∂Pκ) * ∫ ωs, X b ωs ∂Pκ :=
        (hIndep.indepFun_mul_left hMeas a a b hab hab).integral_mul_eq_mul_integral
          ((hAEStrong a).mul (hAEStrong a)) (hAEStrong b)
      have hz :
          ∫ ωs, X a ωs * X b ωs * X a ωs ∂Pκ = 0 := by
        calc
          ∫ ωs, X a ωs * X b ωs * X a ωs ∂Pκ =
              ∫ ωs, (X a * X a) ωs * X b ωs ∂Pκ := by
                congr with ωs
                change X a ωs * X b ωs * X a ωs =
                  (X a ωs * X a ωs) * X b ωs
                ring
          _ = (∫ ωs, (X a * X a) ωs ∂Pκ) * ∫ ωs, X b ωs ∂Pκ := hmul
          _ = 0 := by rw [hmean b, mul_zero]
      rw [if_neg (by intro h; exact hab h.1)]
      simpa [X, Pκ] using hz
    · have hmul :
          ∫ ωs, X a ωs * (X b * X c) ωs ∂Pκ =
            (∫ ωs, X a ωs ∂Pκ) * ∫ ωs, (X b * X c) ωs ∂Pκ :=
        (hIndep.indepFun_mul_right hMeas a b c hab hac).integral_mul_eq_mul_integral
          (hAEStrong a) ((hAEStrong b).mul (hAEStrong c))
      have hz :
          ∫ ωs, X a ωs * X b ωs * X c ωs ∂Pκ = 0 := by
        calc
          ∫ ωs, X a ωs * X b ωs * X c ωs ∂Pκ =
              ∫ ωs, X a ωs * (X b * X c) ωs ∂Pκ := by
                congr with ωs
                change X a ωs * X b ωs * X c ωs =
                  X a ωs * (X b ωs * X c ωs)
                ring
          _ = (∫ ωs, X a ωs ∂Pκ) * ∫ ωs, (X b * X c) ωs ∂Pκ := hmul
          _ = 0 := by rw [hmean a, zero_mul]
      rw [if_neg (by intro h; exact hab h.1)]
      simpa [X, Pκ] using hz

/-- Quadruple product of centered ordinary-bootstrap coordinates.

The nonzero conditional fourth-moment terms are the all-equal case and the
three ordered two-pair partitions. All remaining terms contain a centered
singleton coordinate and vanish by independence. -/
theorem integral_mul_mul_mul_uniformOn_fun_eval_sub_empiricalMean_eq
    {κ : Type*} [Finite κ] [DecidableEq κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (a b c d : κ) :
    ∫ ωs : κ → ι,
        (Y (ωs a) - empiricalMean Y) *
          (Y (ωs b) - empiricalMean Y) *
          (Y (ωs c) - empiricalMean Y) *
          (Y (ωs d) - empiricalMean Y)
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      if a = b ∧ a = c ∧ a = d then
        empiricalCentralMoment Y 4
      else if a = b ∧ c = d ∧ a ≠ c then
        empiricalCumulant2 Y ^ 2
      else if a = c ∧ b = d ∧ a ≠ b then
        empiricalCumulant2 Y ^ 2
      else if a = d ∧ b = c ∧ a ≠ b then
        empiricalCumulant2 Y ^ 2
      else
        0 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  have hIndep : iIndepFun X Pκ := by
    simpa [X, Pκ] using
      (iIndepFun_uniformOn_fun_eval_sub_empiricalMean
        (κ := κ) (ι := ι) (E := ℝ) Y)
  have hMeas : ∀ t : κ, Measurable (X t) := fun t =>
    measurable_of_finite (X t)
  have hAEStrong : ∀ t : κ, AEStronglyMeasurable (X t) Pκ := fun t =>
    (hMeas t).aestronglyMeasurable
  have hmean : ∀ t : κ, ∫ ωs, X t ωs ∂Pκ = 0 := by
    intro t
    have hbase :
        ∫ ωs : κ → ι, Y (ωs t) ∂Pκ = empiricalMean Y := by
      simpa [Pκ] using
        (integral_uniformOn_fun_eval_eq_empiricalMean
          (κ := κ) (Y := Y) t)
    have hInt : Integrable (fun ωs : κ → ι => Y (ωs t)) Pκ :=
      Integrable.of_finite
    calc
      ∫ ωs, X t ωs ∂Pκ =
          ∫ ωs : κ → ι, Y (ωs t) - empiricalMean Y ∂Pκ := rfl
      _ = ∫ ωs : κ → ι, Y (ωs t) ∂Pκ - ∫ _ωs : κ → ι, empiricalMean Y ∂Pκ := by
          rw [integral_sub hInt (integrable_const _)]
      _ = 0 := by
          rw [hbase]
          simp [Pκ]
  have hsecond : ∀ t : κ,
      ∫ ωs, X t ωs * X t ωs ∂Pκ = empiricalCumulant2 Y := by
    intro t
    simpa [X, Pκ] using
      (integral_mul_uniformOn_fun_eval_sub_empiricalMean_eq
        (κ := κ) (Y := Y) t t)
  have hfourth : ∀ t : κ,
      ∫ ωs, X t ωs ^ 4 ∂Pκ = empiricalCentralMoment Y 4 := by
    intro t
    change
      ∫ ωs : κ → ι, (Y (ωs t) - empiricalMean Y) ^ 4
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        empiricalCentralMoment Y 4
    exact
      integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) t 4
  have hsingleton : ∀ s u v w : κ, s ≠ u → s ≠ v → s ≠ w →
      ∫ ωs, X s ωs * X u ωs * X v ωs * X w ωs ∂Pκ = 0 := by
    intro s u v w hsu hsv hsw
    let S : Finset κ := {s}
    let T : Finset κ := {u, v, w}
    have hST : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      have hxs : x = s := by
        simpa [S] using hxS
      subst x
      have hsT : s ∈ T := hxT
      simp [T, hsu, hsv, hsw] at hsT
    let φ : (S → ℝ) → ℝ := fun z => z ⟨s, by simp [S]⟩
    let ψ : (T → ℝ) → ℝ :=
      fun z => z ⟨u, by simp [T]⟩ * z ⟨v, by simp [T]⟩ * z ⟨w, by simp [T]⟩
    have hφ : Measurable φ := by
      dsimp [φ]
      exact measurable_pi_apply (X := fun _ : S => ℝ) (⟨s, by simp [S]⟩ : S)
    have hψ : Measurable ψ := by
      dsimp [ψ]
      exact
        ((measurable_pi_apply (X := fun _ : T => ℝ) (⟨u, by simp [T]⟩ : T)).mul
          (measurable_pi_apply (X := fun _ : T => ℝ) (⟨v, by simp [T]⟩ : T))).mul
            (measurable_pi_apply (X := fun _ : T => ℝ) (⟨w, by simp [T]⟩ : T))
    have hind :
        IndepFun (X s) (fun ωs => X u ωs * X v ωs * X w ωs) Pκ := by
      simpa [φ, ψ, S, T, Function.comp_def] using
        (hIndep.indepFun_finset S T hST hMeas).comp hφ hψ
    have hfac :
        ∫ ωs, X s ωs * (X u ωs * X v ωs * X w ωs) ∂Pκ =
          (∫ ωs, X s ωs ∂Pκ) *
            ∫ ωs, X u ωs * X v ωs * X w ωs ∂Pκ :=
      hind.integral_mul_eq_mul_integral
        (hAEStrong s) (((hAEStrong u).mul (hAEStrong v)).mul (hAEStrong w))
    calc
      ∫ ωs, X s ωs * X u ωs * X v ωs * X w ωs ∂Pκ =
          ∫ ωs, X s ωs * (X u ωs * X v ωs * X w ωs) ∂Pκ := by
            congr with ωs
            ring
      _ = (∫ ωs, X s ωs ∂Pκ) *
            ∫ ωs, X u ωs * X v ωs * X w ωs ∂Pκ := hfac
      _ = 0 := by rw [hmean s, zero_mul]
  have hpair : ∀ p q : κ, p ≠ q →
      ∫ ωs, X p ωs * X p ωs * X q ωs * X q ωs ∂Pκ =
        empiricalCumulant2 Y ^ 2 := by
    intro p q hpq
    have hmul :
        ∫ ωs, (X p * X p) ωs * (X q * X q) ωs ∂Pκ =
          (∫ ωs, (X p * X p) ωs ∂Pκ) *
            ∫ ωs, (X q * X q) ωs ∂Pκ :=
      (hIndep.indepFun_mul_mul hMeas p p q q hpq hpq hpq hpq).integral_mul_eq_mul_integral
        ((hAEStrong p).mul (hAEStrong p)) ((hAEStrong q).mul (hAEStrong q))
    calc
      ∫ ωs, X p ωs * X p ωs * X q ωs * X q ωs ∂Pκ =
          ∫ ωs, (X p * X p) ωs * (X q * X q) ωs ∂Pκ := by
            congr with ωs
            simp [Pi.mul_apply]
            ring
      _ = (∫ ωs, (X p * X p) ωs ∂Pκ) *
            ∫ ωs, (X q * X q) ωs ∂Pκ := hmul
      _ = empiricalCumulant2 Y ^ 2 := by
            change
              (∫ ωs, X p ωs * X p ωs ∂Pκ) *
                ∫ ωs, X q ωs * X q ωs ∂Pκ = empiricalCumulant2 Y ^ 2
            rw [hsecond p, hsecond q]
            ring
  by_cases hAll : a = b ∧ a = c ∧ a = d
  · rw [if_pos hAll]
    rcases hAll with ⟨hab, hac, had⟩
    subst b
    subst c
    subst d
    change ∫ ωs, X a ωs * X a ωs * X a ωs * X a ωs ∂Pκ =
      empiricalCentralMoment Y 4
    calc
      ∫ ωs, X a ωs * X a ωs * X a ωs * X a ωs ∂Pκ =
          ∫ ωs, X a ωs ^ 4 ∂Pκ := by
            congr with ωs
            ring
      _ = empiricalCentralMoment Y 4 := hfourth a
  · rw [if_neg hAll]
    by_cases hABCD : a = b ∧ c = d ∧ a ≠ c
    · rw [if_pos hABCD]
      rcases hABCD with ⟨hab, hcd, hac⟩
      subst b
      subst d
      change ∫ ωs, X a ωs * X a ωs * X c ωs * X c ωs ∂Pκ =
        empiricalCumulant2 Y ^ 2
      exact hpair a c hac
    · rw [if_neg hABCD]
      by_cases hACBD : a = c ∧ b = d ∧ a ≠ b
      · rw [if_pos hACBD]
        rcases hACBD with ⟨hac, hbd, hab⟩
        subst c
        subst d
        change ∫ ωs, X a ωs * X b ωs * X a ωs * X b ωs ∂Pκ =
          empiricalCumulant2 Y ^ 2
        calc
          ∫ ωs, X a ωs * X b ωs * X a ωs * X b ωs ∂Pκ =
              ∫ ωs, X a ωs * X a ωs * X b ωs * X b ωs ∂Pκ := by
                congr with ωs
                ring
          _ = empiricalCumulant2 Y ^ 2 := hpair a b hab
      · rw [if_neg hACBD]
        by_cases hADBC : a = d ∧ b = c ∧ a ≠ b
        · rw [if_pos hADBC]
          rcases hADBC with ⟨had, hbc, hab⟩
          subst d
          subst c
          change ∫ ωs, X a ωs * X b ωs * X b ωs * X a ωs ∂Pκ =
            empiricalCumulant2 Y ^ 2
          calc
            ∫ ωs, X a ωs * X b ωs * X b ωs * X a ωs ∂Pκ =
                ∫ ωs, X a ωs * X a ωs * X b ωs * X b ωs ∂Pκ := by
                  congr with ωs
                  ring
            _ = empiricalCumulant2 Y ^ 2 := hpair a b hab
        · rw [if_neg hADBC]
          rcases
              exists_singleton_of_not_allEqual4_not_pairPatterns
                hAll hABCD hACBD hADBC with
            ha | hrest
          · change ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ = 0
            exact hsingleton a b c d ha.1 ha.2.1 ha.2.2
          · rcases hrest with hb | hrest
            · change ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ = 0
              calc
                ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ =
                    ∫ ωs, X b ωs * X a ωs * X c ωs * X d ωs ∂Pκ := by
                      congr with ωs
                      ring
                _ = 0 := hsingleton b a c d hb.1 hb.2.1 hb.2.2
            · rcases hrest with hc | hd
              · change ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ = 0
                calc
                  ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ =
                      ∫ ωs, X c ωs * X a ωs * X b ωs * X d ωs ∂Pκ := by
                        congr with ωs
                        ring
                  _ = 0 := hsingleton c a b d hc.1 hc.2.1 hc.2.2
              · change ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ = 0
                calc
                  ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ =
                      ∫ ωs, X d ωs * X a ωs * X b ωs * X c ωs ∂Pκ := by
                        congr with ωs
                        ring
                  _ = 0 := hsingleton d a b c hd.1 hd.2.1 hd.2.2

/-- Quintuple product of centered ordinary-bootstrap coordinates.

The nonzero conditional fifth-moment terms are the all-equal case and the ten
ordered triple-pair partitions. All remaining terms contain a centered
singleton coordinate and vanish by independence. -/
theorem integral_mul_mul_mul_mul_uniformOn_fun_eval_sub_empiricalMean_eq
    {κ : Type*} [Finite κ] [DecidableEq κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (a b c d e : κ) :
    ∫ ωs : κ → ι,
        (Y (ωs a) - empiricalMean Y) *
          (Y (ωs b) - empiricalMean Y) *
          (Y (ωs c) - empiricalMean Y) *
          (Y (ωs d) - empiricalMean Y) *
          (Y (ωs e) - empiricalMean Y)
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      (if a = b ∧ a = c ∧ a = d ∧ a = e then
        empiricalCentralMoment Y 5 else 0) +
      (if a = b ∧ a = c ∧ d = e ∧ a ≠ d then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if a = b ∧ a = d ∧ c = e ∧ a ≠ c then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if a = b ∧ a = e ∧ c = d ∧ a ≠ c then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if a = c ∧ a = d ∧ b = e ∧ a ≠ b then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if a = c ∧ a = e ∧ b = d ∧ a ≠ b then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if a = d ∧ a = e ∧ b = c ∧ a ≠ b then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if b = c ∧ b = d ∧ a = e ∧ b ≠ a then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if b = c ∧ b = e ∧ a = d ∧ b ≠ a then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if b = d ∧ b = e ∧ a = c ∧ b ≠ a then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) +
      (if c = d ∧ c = e ∧ a = b ∧ c ≠ a then
        empiricalCumulant3 Y * empiricalCumulant2 Y else 0) := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  let m32 : ℝ := empiricalCumulant3 Y * empiricalCumulant2 Y
  have hIndep : iIndepFun X Pκ := by
    simpa [X, Pκ] using
      (iIndepFun_uniformOn_fun_eval_sub_empiricalMean
        (κ := κ) (ι := ι) (E := ℝ) Y)
  have hMeas : ∀ t : κ, Measurable (X t) := fun t =>
    measurable_of_finite (X t)
  have hAEStrong : ∀ t : κ, AEStronglyMeasurable (X t) Pκ := fun t =>
    (hMeas t).aestronglyMeasurable
  have hmean : ∀ t : κ, ∫ ωs, X t ωs ∂Pκ = 0 := by
    intro t
    have hbase :
        ∫ ωs : κ → ι, Y (ωs t) ∂Pκ = empiricalMean Y := by
      simpa [Pκ] using
        (integral_uniformOn_fun_eval_eq_empiricalMean
          (κ := κ) (Y := Y) t)
    have hInt : Integrable (fun ωs : κ → ι => Y (ωs t)) Pκ :=
      Integrable.of_finite
    calc
      ∫ ωs, X t ωs ∂Pκ =
          ∫ ωs : κ → ι, Y (ωs t) - empiricalMean Y ∂Pκ := rfl
      _ = ∫ ωs : κ → ι, Y (ωs t) ∂Pκ - ∫ _ωs : κ → ι, empiricalMean Y ∂Pκ := by
          rw [integral_sub hInt (integrable_const _)]
      _ = 0 := by
          rw [hbase]
          simp [Pκ]
  have hsecond : ∀ t : κ,
      ∫ ωs, X t ωs ^ 2 ∂Pκ = empiricalCumulant2 Y := by
    intro t
    change
      ∫ ωs : κ → ι, (Y (ωs t) - empiricalMean Y) ^ 2
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        empiricalCumulant2 Y
    exact
      integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) t 2
  have hthird : ∀ t : κ,
      ∫ ωs, X t ωs ^ 3 ∂Pκ = empiricalCumulant3 Y := by
    intro t
    change
      ∫ ωs : κ → ι, (Y (ωs t) - empiricalMean Y) ^ 3
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        empiricalCumulant3 Y
    rw [← empiricalCentralMoment_three_eq_cumulant3 Y]
    exact
      integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) t 3
  have hfifth : ∀ t : κ,
      ∫ ωs, X t ωs ^ 5 ∂Pκ = empiricalCentralMoment Y 5 := by
    intro t
    change
      ∫ ωs : κ → ι, (Y (ωs t) - empiricalMean Y) ^ 5
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        empiricalCentralMoment Y 5
    exact
      integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) t 5
  have hsingleton : ∀ s u v w z : κ, s ≠ u → s ≠ v → s ≠ w → s ≠ z →
      ∫ ωs, X s ωs * X u ωs * X v ωs * X w ωs * X z ωs ∂Pκ = 0 := by
    intro s u v w z hsu hsv hsw hsz
    let S : Finset κ := {s}
    let T : Finset κ := {u, v, w, z}
    have hST : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      have hxs : x = s := by
        simpa [S] using hxS
      subst x
      have hsT : s ∈ T := hxT
      simp [T, hsu, hsv, hsw, hsz] at hsT
    let φ : (S → ℝ) → ℝ := fun y => y ⟨s, by simp [S]⟩
    let ψ : (T → ℝ) → ℝ :=
      fun y =>
        y ⟨u, by simp [T]⟩ * y ⟨v, by simp [T]⟩ *
          y ⟨w, by simp [T]⟩ * y ⟨z, by simp [T]⟩
    have hφ : Measurable φ := by
      dsimp [φ]
      exact measurable_pi_apply (X := fun _ : S => ℝ) (⟨s, by simp [S]⟩ : S)
    have hψ : Measurable ψ := by
      dsimp [ψ]
      exact
        (((measurable_pi_apply (X := fun _ : T => ℝ) (⟨u, by simp [T]⟩ : T)).mul
          (measurable_pi_apply (X := fun _ : T => ℝ) (⟨v, by simp [T]⟩ : T))).mul
            (measurable_pi_apply (X := fun _ : T => ℝ) (⟨w, by simp [T]⟩ : T))).mul
              (measurable_pi_apply (X := fun _ : T => ℝ) (⟨z, by simp [T]⟩ : T))
    have hind :
        IndepFun (X s) (fun ωs => X u ωs * X v ωs * X w ωs * X z ωs) Pκ := by
      simpa [φ, ψ, S, T, Function.comp_def, mul_assoc] using
        (hIndep.indepFun_finset S T hST hMeas).comp hφ hψ
    have hfac :
        ∫ ωs, X s ωs * (X u ωs * X v ωs * X w ωs * X z ωs) ∂Pκ =
          (∫ ωs, X s ωs ∂Pκ) *
            ∫ ωs, X u ωs * X v ωs * X w ωs * X z ωs ∂Pκ :=
      hind.integral_mul_eq_mul_integral
        (hAEStrong s) ((((hAEStrong u).mul (hAEStrong v)).mul (hAEStrong w)).mul
          (hAEStrong z))
    calc
      ∫ ωs, X s ωs * X u ωs * X v ωs * X w ωs * X z ωs ∂Pκ =
          ∫ ωs, X s ωs * (X u ωs * X v ωs * X w ωs * X z ωs) ∂Pκ := by
            congr with ωs
            ring
      _ = (∫ ωs, X s ωs ∂Pκ) *
            ∫ ωs, X u ωs * X v ωs * X w ωs * X z ωs ∂Pκ := hfac
      _ = 0 := by rw [hmean s, zero_mul]
  have htriplePair : ∀ p q : κ, p ≠ q →
      ∫ ωs, X p ωs * X p ωs * X p ωs * X q ωs * X q ωs ∂Pκ =
        m32 := by
    intro p q hpq
    have hind :
        IndepFun (fun ωs => X p ωs ^ 3) (fun ωs => X q ωs ^ 2) Pκ :=
      (hIndep.indepFun hpq).comp
        (measurable_id.pow_const 3) (measurable_id.pow_const 2)
    have hfac :
        ∫ ωs, X p ωs ^ 3 * X q ωs ^ 2 ∂Pκ =
          (∫ ωs, X p ωs ^ 3 ∂Pκ) *
            ∫ ωs, X q ωs ^ 2 ∂Pκ :=
      hind.integral_mul_eq_mul_integral
        (measurable_of_finite (fun ωs : κ → ι => X p ωs ^ 3)).aestronglyMeasurable
        (measurable_of_finite (fun ωs : κ → ι => X q ωs ^ 2)).aestronglyMeasurable
    calc
      ∫ ωs, X p ωs * X p ωs * X p ωs * X q ωs * X q ωs ∂Pκ =
          ∫ ωs, X p ωs ^ 3 * X q ωs ^ 2 ∂Pκ := by
            congr with ωs
            ring
      _ = (∫ ωs, X p ωs ^ 3 ∂Pκ) * ∫ ωs, X q ωs ^ 2 ∂Pκ := hfac
      _ = m32 := by
            rw [hthird p, hsecond q]
  by_cases hAll : a = b ∧ a = c ∧ a = d ∧ a = e
  · rcases hAll with ⟨hab, hac, had, hae⟩
    subst b
    subst c
    subst d
    subst e
    change ∫ ωs, X a ωs * X a ωs * X a ωs * X a ωs * X a ωs ∂Pκ =
      (if a = a ∧ a = a ∧ a = a ∧ a = a then empiricalCentralMoment Y 5 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0) +
      (if a = a ∧ a = a ∧ a = a ∧ a ≠ a then m32 else 0)
    suffices
        ∫ ωs, X a ωs * X a ωs * X a ωs * X a ωs * X a ωs ∂Pκ =
          empiricalCentralMoment Y 5 by
      simpa only [and_self, ↓reduceIte, ne_eq, not_true_eq_false, and_false, add_zero]
        using this
    calc
      ∫ ωs, X a ωs * X a ωs * X a ωs * X a ωs * X a ωs ∂Pκ =
          ∫ ωs, X a ωs ^ 5 ∂Pκ := by
            congr with ωs
            ring
      _ = empiricalCentralMoment Y 5 := hfifth a
  · by_cases hABC_DE : a = b ∧ a = c ∧ d = e ∧ a ≠ d
    · rcases hABC_DE with ⟨hab, hac, hde, had⟩
      subst b
      subst c
      subst e
      change ∫ ωs, X a ωs * X a ωs * X a ωs * X d ωs * X d ωs ∂Pκ = _
      rw [htriplePair a d had]
      simp [m32, had]
    · by_cases hABD_CE : a = b ∧ a = d ∧ c = e ∧ a ≠ c
      · rcases hABD_CE with ⟨hab, had, hce, hac⟩
        subst b
        subst d
        subst e
        change ∫ ωs, X a ωs * X a ωs * X c ωs * X a ωs * X c ωs ∂Pκ = _
        calc
          ∫ ωs, X a ωs * X a ωs * X c ωs * X a ωs * X c ωs ∂Pκ =
              ∫ ωs, X a ωs * X a ωs * X a ωs * X c ωs * X c ωs ∂Pκ := by
                congr with ωs
                ring
          _ = _ := by
                rw [htriplePair a c hac]
                simp [m32, hac]
      · by_cases hABE_CD : a = b ∧ a = e ∧ c = d ∧ a ≠ c
        · rcases hABE_CD with ⟨hab, hae, hcd, hac⟩
          subst b
          subst e
          subst d
          change ∫ ωs, X a ωs * X a ωs * X c ωs * X c ωs * X a ωs ∂Pκ = _
          calc
            ∫ ωs, X a ωs * X a ωs * X c ωs * X c ωs * X a ωs ∂Pκ =
                ∫ ωs, X a ωs * X a ωs * X a ωs * X c ωs * X c ωs ∂Pκ := by
                  congr with ωs
                  ring
            _ = _ := by
                  rw [htriplePair a c hac]
                  simp [m32, hac]
        · by_cases hACD_BE : a = c ∧ a = d ∧ b = e ∧ a ≠ b
          · rcases hACD_BE with ⟨hac, had, hbe, hab⟩
            subst c
            subst d
            subst e
            change ∫ ωs, X a ωs * X b ωs * X a ωs * X a ωs * X b ωs ∂Pκ = _
            calc
              ∫ ωs, X a ωs * X b ωs * X a ωs * X a ωs * X b ωs ∂Pκ =
                  ∫ ωs, X a ωs * X a ωs * X a ωs * X b ωs * X b ωs ∂Pκ := by
                    congr with ωs
                    ring
              _ = _ := by
                    rw [htriplePair a b hab]
                    simp [m32, hab]
          · by_cases hACE_BD : a = c ∧ a = e ∧ b = d ∧ a ≠ b
            · rcases hACE_BD with ⟨hac, hae, hbd, hab⟩
              subst c
              subst e
              subst d
              change ∫ ωs, X a ωs * X b ωs * X a ωs * X b ωs * X a ωs ∂Pκ = _
              calc
                ∫ ωs, X a ωs * X b ωs * X a ωs * X b ωs * X a ωs ∂Pκ =
                    ∫ ωs, X a ωs * X a ωs * X a ωs * X b ωs * X b ωs ∂Pκ := by
                      congr with ωs
                      ring
                _ = _ := by
                      rw [htriplePair a b hab]
                      simp [m32, hab]
            · by_cases hADE_BC : a = d ∧ a = e ∧ b = c ∧ a ≠ b
              · rcases hADE_BC with ⟨had, hae, hbc, hab⟩
                subst d
                subst e
                subst c
                change ∫ ωs, X a ωs * X b ωs * X b ωs * X a ωs * X a ωs ∂Pκ = _
                calc
                  ∫ ωs, X a ωs * X b ωs * X b ωs * X a ωs * X a ωs ∂Pκ =
                      ∫ ωs, X a ωs * X a ωs * X a ωs * X b ωs * X b ωs ∂Pκ := by
                        congr with ωs
                        ring
                  _ = _ := by
                        rw [htriplePair a b hab]
                        simp [m32, hab]
              · by_cases hBCD_AE : b = c ∧ b = d ∧ a = e ∧ b ≠ a
                · rcases hBCD_AE with ⟨hbc, hbd, hae, hba⟩
                  subst c
                  subst d
                  subst e
                  change ∫ ωs, X a ωs * X b ωs * X b ωs * X b ωs * X a ωs ∂Pκ = _
                  calc
                    ∫ ωs, X a ωs * X b ωs * X b ωs * X b ωs * X a ωs ∂Pκ =
                        ∫ ωs, X b ωs * X b ωs * X b ωs * X a ωs * X a ωs ∂Pκ := by
                          congr with ωs
                          ring
                    _ = _ := by
                          rw [htriplePair b a hba]
                          have hab : a ≠ b := hba.symm
                          simp [m32, hba, hab]
                · by_cases hBCE_AD : b = c ∧ b = e ∧ a = d ∧ b ≠ a
                  · rcases hBCE_AD with ⟨hbc, hbe, had, hba⟩
                    subst c
                    subst e
                    subst d
                    change ∫ ωs, X a ωs * X b ωs * X b ωs * X a ωs * X b ωs ∂Pκ = _
                    calc
                      ∫ ωs, X a ωs * X b ωs * X b ωs * X a ωs * X b ωs ∂Pκ =
                          ∫ ωs, X b ωs * X b ωs * X b ωs * X a ωs * X a ωs ∂Pκ := by
                            congr with ωs
                            ring
                      _ = _ := by
                            rw [htriplePair b a hba]
                            have hab : a ≠ b := hba.symm
                            simp [m32, hba, hab]
                  · by_cases hBDE_AC : b = d ∧ b = e ∧ a = c ∧ b ≠ a
                    · rcases hBDE_AC with ⟨hbd, hbe, hac, hba⟩
                      subst d
                      subst e
                      subst c
                      change ∫ ωs, X a ωs * X b ωs * X a ωs * X b ωs * X b ωs ∂Pκ = _
                      calc
                        ∫ ωs, X a ωs * X b ωs * X a ωs * X b ωs * X b ωs ∂Pκ =
                            ∫ ωs, X b ωs * X b ωs * X b ωs * X a ωs * X a ωs ∂Pκ := by
                              congr with ωs
                              ring
                        _ = _ := by
                              rw [htriplePair b a hba]
                              have hab : a ≠ b := hba.symm
                              simp [m32, hba, hab]
                    · by_cases hCDE_AB : c = d ∧ c = e ∧ a = b ∧ c ≠ a
                      · rcases hCDE_AB with ⟨hcd, hce, hab, hca⟩
                        subst d
                        subst e
                        subst b
                        change ∫ ωs, X a ωs * X a ωs * X c ωs * X c ωs * X c ωs ∂Pκ = _
                        calc
                          ∫ ωs, X a ωs * X a ωs * X c ωs * X c ωs * X c ωs ∂Pκ =
                              ∫ ωs, X c ωs * X c ωs * X c ωs * X a ωs * X a ωs ∂Pκ := by
                                congr with ωs
                                ring
                          _ = _ := by
                                rw [htriplePair c a hca]
                                have hac : a ≠ c := hca.symm
                                simp [m32, hca, hac]
                      · suffices
                            ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ =
                              0 by
                          simpa [
                            hAll, hABC_DE, hABD_CE, hABE_CD, hACD_BE, hACE_BD,
                            hADE_BC, hBCD_AE, hBCE_AD, hBDE_AC, hCDE_AB] using this
                        rcases
                            exists_singleton_of_not_allEqual5_not_triplePairPatterns
                              hAll hABC_DE hABD_CE hABE_CD hACD_BE hACE_BD
                              hADE_BC hBCD_AE hBCE_AD hBDE_AC hCDE_AB with
                          ha | hrest
                        · exact hsingleton a b c d e ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
                        · rcases hrest with hb | hrest
                          · calc
                              ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ =
                                  ∫ ωs, X b ωs * X a ωs * X c ωs * X d ωs * X e ωs ∂Pκ := by
                                    congr with ωs
                                    ring
                              _ = 0 := hsingleton b a c d e hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
                          · rcases hrest with hc | hrest
                            · calc
                                ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ =
                                    ∫ ωs, X c ωs * X a ωs * X b ωs * X d ωs * X e ωs ∂Pκ := by
                                      congr with ωs
                                      ring
                                _ = 0 := hsingleton c a b d e hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
                            · rcases hrest with hd | he
                              · calc
                                  ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ =
                                      ∫ ωs, X d ωs * X a ωs * X b ωs * X c ωs * X e ωs ∂Pκ := by
                                        congr with ωs
                                        ring
                                  _ = 0 := hsingleton d a b c e hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
                              · calc
                                  ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ =
                                      ∫ ωs, X e ωs * X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ := by
                                        congr with ωs
                                        ring
                                  _ = 0 := hsingleton e a b c d he.1 he.2.1 he.2.2.1 he.2.2.2

/-- Second moment of the centered ordinary-bootstrap sum with one coordinate
removed. -/
private theorem integral_sq_centered_uniformOn_fun_sum_erase_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (a : κ) :
    ∫ ωs : κ → ι,
        (∑ t ∈ Finset.univ.erase a, (Y (ωs t) - empiricalMean Y)) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      ((Fintype.card κ : ℝ) - 1) * empiricalCumulant2 Y := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  let s : Finset κ := Finset.univ.erase a
  have hsquare : ∀ ωs : κ → ι,
      (∑ t ∈ s, X t ωs) ^ 2 =
        ∑ b ∈ s, ∑ c ∈ s, X b ωs * X c ωs := by
    intro ωs
    simp [pow_succ, Finset.mul_sum, mul_comm]
  have hpair : ∀ b c : κ,
      ∫ ωs, X b ωs * X c ωs ∂Pκ =
        if b = c then empiricalCumulant2 Y else 0 := by
    intro b c
    simpa [X, Pκ] using
      integral_mul_uniformOn_fun_eval_sub_empiricalMean_eq
        (κ := κ) (Y := Y) b c
  have hdiag :
      (∑ b ∈ s, ∑ c ∈ s, if b = c then empiricalCumulant2 Y else 0) =
        (s.card : ℝ) * empiricalCumulant2 Y := by
    calc
      (∑ b ∈ s, ∑ c ∈ s, if b = c then empiricalCumulant2 Y else 0) =
          ∑ b ∈ s, empiricalCumulant2 Y := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_eq_single b]
          · simp
          · intro c hc hcb
            have hbc : b ≠ c := fun h => hcb h.symm
            simp [hbc]
          · intro hbnone
            exact (hbnone hb).elim
      _ = (s.card : ℝ) * empiricalCumulant2 Y := by
          simp
  calc
    ∫ ωs : κ → ι,
        (∑ t ∈ Finset.univ.erase a, (Y (ωs t) - empiricalMean Y)) ^ 2 ∂Pκ =
        ∫ ωs : κ → ι, (∑ t ∈ s, X t ωs) ^ 2 ∂Pκ := by
          simp [s, X]
    _ = ∫ ωs : κ → ι, ∑ b ∈ s, ∑ c ∈ s, X b ωs * X c ωs ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hsquare]
    _ = ∑ b ∈ s, ∑ c ∈ s,
          ∫ ωs : κ → ι, X b ωs * X c ωs ∂Pκ := by
          rw [integral_finset_sum (s := s)
            (f := fun b ωs => ∑ c ∈ s, X b ωs * X c ωs)
            (μ := Pκ)
            (hf := by
              intro b _hb
              exact integrable_finset_sum (s := s)
                (f := fun c ωs => X b ωs * X c ωs)
                (fun c _hc => Integrable.of_finite))]
          congr with b
          rw [integral_finset_sum (s := s)
            (f := fun c ωs => X b ωs * X c ωs)
            (μ := Pκ)
            (hf := by
              intro c _hc
              exact Integrable.of_finite)]
    _ = ∑ b ∈ s, ∑ c ∈ s, if b = c then empiricalCumulant2 Y else 0 := by
          simp [hpair]
    _ = (s.card : ℝ) * empiricalCumulant2 Y := hdiag
    _ = ((Fintype.card κ : ℝ) - 1) * empiricalCumulant2 Y := by
          have hcard_one : 1 ≤ Fintype.card κ :=
            Nat.succ_le_of_lt Fintype.card_pos
          dsimp [s]
          rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
          rw [Finset.card_univ]
          rw [Nat.cast_sub hcard_one]
          norm_num

/-- Third moment of the centered ordinary-bootstrap sum with one coordinate
removed. -/
private theorem integral_cube_centered_uniformOn_fun_sum_erase_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (a : κ) :
    ∫ ωs : κ → ι,
        (∑ t ∈ Finset.univ.erase a, (Y (ωs t) - empiricalMean Y)) ^ 3
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      ((Fintype.card κ : ℝ) - 1) * empiricalCumulant3 Y := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  let s : Finset κ := Finset.univ.erase a
  have hcube : ∀ ωs : κ → ι,
      (∑ t ∈ s, X t ωs) ^ 3 =
        ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
          X b ωs * X c ωs * X d ωs := by
    intro ωs
    simp [pow_succ, Finset.mul_sum, mul_comm]
  have htriple : ∀ b c d : κ,
      ∫ ωs, X b ωs * X c ωs * X d ωs ∂Pκ =
        if b = c ∧ b = d then empiricalCumulant3 Y else 0 := by
    intro b c d
    simpa [X, Pκ] using
      integral_mul_mul_uniformOn_fun_eval_sub_empiricalMean_eq
        (κ := κ) (Y := Y) b c d
  have hdiag :
      (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        if b = c ∧ b = d then empiricalCumulant3 Y else 0) =
        (s.card : ℝ) * empiricalCumulant3 Y := by
    have hinner : ∀ b ∈ s,
        (∑ c ∈ s, ∑ d ∈ s,
          if b = c ∧ b = d then empiricalCumulant3 Y else 0) =
          empiricalCumulant3 Y := by
      intro b hb
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single b]
        · simp
        · intro d hd hdb
          have hbd : b ≠ d := fun h => hdb h.symm
          simp [hbd]
        · intro hbnone
          exact (hbnone hb).elim
      · intro c hc hcb
        have hbc : b ≠ c := fun h => hcb h.symm
        simp [hbc]
      · intro hbnone
        exact (hbnone hb).elim
    calc
      (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
          if b = c ∧ b = d then empiricalCumulant3 Y else 0) =
          ∑ b ∈ s, empiricalCumulant3 Y := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hinner b hb
      _ = (s.card : ℝ) * empiricalCumulant3 Y := by
          simp
  calc
    ∫ ωs : κ → ι,
        (∑ t ∈ Finset.univ.erase a, (Y (ωs t) - empiricalMean Y)) ^ 3 ∂Pκ =
        ∫ ωs : κ → ι, (∑ t ∈ s, X t ωs) ^ 3 ∂Pκ := by
          simp [s, X]
    _ = ∫ ωs : κ → ι, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
          X b ωs * X c ωs * X d ωs ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hcube]
    _ = ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
          ∫ ωs : κ → ι, X b ωs * X c ωs * X d ωs ∂Pκ := by
          rw [integral_finset_sum (s := s)
            (f := fun b ωs => ∑ c ∈ s, ∑ d ∈ s, X b ωs * X c ωs * X d ωs)
            (μ := Pκ)
            (hf := by
              intro b _hb
              exact integrable_finset_sum (s := s)
                (f := fun c ωs => ∑ d ∈ s, X b ωs * X c ωs * X d ωs)
                (fun c _hc =>
                  integrable_finset_sum (s := s)
                    (f := fun d ωs => X b ωs * X c ωs * X d ωs)
                    (fun d _hd => Integrable.of_finite)))]
          congr with b
          rw [integral_finset_sum (s := s)
            (f := fun c ωs => ∑ d ∈ s, X b ωs * X c ωs * X d ωs)
            (μ := Pκ)
            (hf := by
              intro c _hc
              exact integrable_finset_sum (s := s)
                (f := fun d ωs => X b ωs * X c ωs * X d ωs)
                (fun d _hd => Integrable.of_finite))]
          congr with c
          rw [integral_finset_sum (s := s)
            (f := fun d ωs => X b ωs * X c ωs * X d ωs)
            (μ := Pκ)
            (hf := by
              intro d _hd
              exact Integrable.of_finite)]
    _ = ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
          if b = c ∧ b = d then empiricalCumulant3 Y else 0 := by
          simp [htriple]
    _ = (s.card : ℝ) * empiricalCumulant3 Y := hdiag
    _ = ((Fintype.card κ : ℝ) - 1) * empiricalCumulant3 Y := by
          have hcard_one : 1 ≤ Fintype.card κ :=
            Nat.succ_le_of_lt Fintype.card_pos
          dsimp [s]
          rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
          rw [Finset.card_univ]
          rw [Nat.cast_sub hcard_one]
          norm_num

/-- Fourth moment of the centered ordinary-bootstrap sum with one coordinate
removed. -/
private theorem integral_fourth_centered_uniformOn_fun_sum_erase_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (a : κ) :
    ∫ ωs : κ → ι,
        (∑ t ∈ Finset.univ.erase a, (Y (ωs t) - empiricalMean Y)) ^ 4
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      ((Fintype.card κ : ℝ) - 1) * empiricalCentralMoment Y 4 +
        3 * ((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 2) *
          empiricalCumulant2 Y ^ 2 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  let s : Finset κ := Finset.univ.erase a
  let μ4 : ℝ := empiricalCentralMoment Y 4
  let v : ℝ := empiricalCumulant2 Y ^ 2
  have hfour : ∀ ωs : κ → ι,
      (∑ t ∈ s, X t ωs) ^ 4 =
        ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
          X b ωs * X c ωs * X d ωs * X e ωs := by
    intro ωs
    simp [pow_succ, Finset.mul_sum, mul_assoc, mul_comm]
  have hquad : ∀ b c d e : κ,
      ∫ ωs, X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ =
        if b = c ∧ b = d ∧ b = e then μ4
        else if b = c ∧ d = e ∧ b ≠ d then v
        else if b = d ∧ c = e ∧ b ≠ c then v
        else if b = e ∧ c = d ∧ b ≠ c then v
        else 0 := by
    intro b c d e
    simpa [X, Pκ, μ4, v] using
      integral_mul_mul_mul_uniformOn_fun_eval_sub_empiricalMean_eq
        (κ := κ) (Y := Y) b c d e
  have hsplit : ∀ b c d e : κ,
      (if b = c ∧ b = d ∧ b = e then μ4
        else if b = c ∧ d = e ∧ b ≠ d then v
        else if b = d ∧ c = e ∧ b ≠ c then v
        else if b = e ∧ c = d ∧ b ≠ c then v
        else 0) =
        (if b = c ∧ b = d ∧ b = e then μ4 else 0) +
          (if b = c ∧ d = e ∧ b ≠ d then v else 0) +
          (if b = d ∧ c = e ∧ b ≠ c then v else 0) +
          (if b = e ∧ c = d ∧ b ≠ c then v else 0) := by
    intro b c d e
    by_cases hAll : b = c ∧ b = d ∧ b = e
    · rcases hAll with ⟨hbc, hbd, hbe⟩
      subst c
      subst d
      subst e
      simp
    · by_cases hABCD : b = c ∧ d = e ∧ b ≠ d
      · rcases hABCD with ⟨hbc, hde, hbd⟩
        subst c
        subst e
        simp [hbd]
      · by_cases hACBD : b = d ∧ c = e ∧ b ≠ c
        · rcases hACBD with ⟨hbd, hce, hbc⟩
          subst d
          subst e
          simp [hbc]
        · by_cases hADBC : b = e ∧ c = d ∧ b ≠ c
          · rcases hADBC with ⟨hbe, hcd, hbc⟩
            subst e
            subst d
            simp [hbc]
          · simp [hAll, hABCD, hACBD, hADBC]
  have hscard :
      (s.card : ℝ) = (Fintype.card κ : ℝ) - 1 := by
    have hcard_one : 1 ≤ Fintype.card κ :=
      Nat.succ_le_of_lt Fintype.card_pos
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
    rw [Finset.card_univ]
    rw [Nat.cast_sub hcard_one]
    norm_num
  calc
    ∫ ωs : κ → ι,
        (∑ t ∈ Finset.univ.erase a, (Y (ωs t) - empiricalMean Y)) ^ 4 ∂Pκ =
        ∫ ωs : κ → ι, (∑ t ∈ s, X t ωs) ^ 4 ∂Pκ := by
          simp [s, X]
    _ = ∫ ωs : κ → ι, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
          X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hfour]
    _ = ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
          ∫ ωs : κ → ι, X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ := by
          rw [integral_finset_sum (s := s)
            (f := fun b ωs => ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
              X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro b _hb
              exact integrable_finset_sum (s := s)
                (f := fun c ωs => ∑ d ∈ s, ∑ e ∈ s,
                  X b ωs * X c ωs * X d ωs * X e ωs)
                (fun c _hc =>
                  integrable_finset_sum (s := s)
                    (f := fun d ωs => ∑ e ∈ s,
                      X b ωs * X c ωs * X d ωs * X e ωs)
                    (fun d _hd =>
                      integrable_finset_sum (s := s)
                        (f := fun e ωs => X b ωs * X c ωs * X d ωs * X e ωs)
                        (fun e _he => Integrable.of_finite))))]
          congr with b
          rw [integral_finset_sum (s := s)
            (f := fun c ωs => ∑ d ∈ s, ∑ e ∈ s,
              X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro c _hc
              exact integrable_finset_sum (s := s)
                (f := fun d ωs => ∑ e ∈ s,
                  X b ωs * X c ωs * X d ωs * X e ωs)
                (fun d _hd =>
                  integrable_finset_sum (s := s)
                    (f := fun e ωs => X b ωs * X c ωs * X d ωs * X e ωs)
                    (fun e _he => Integrable.of_finite)))]
          congr with c
          rw [integral_finset_sum (s := s)
            (f := fun d ωs => ∑ e ∈ s,
              X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro d _hd
              exact integrable_finset_sum (s := s)
                (f := fun e ωs => X b ωs * X c ωs * X d ωs * X e ωs)
                (fun e _he => Integrable.of_finite))]
          congr with d
          rw [integral_finset_sum (s := s)
            (f := fun e ωs => X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro e _he
              exact Integrable.of_finite)]
    _ = ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
          (if b = c ∧ b = d ∧ b = e then μ4
          else if b = c ∧ d = e ∧ b ≠ d then v
          else if b = d ∧ c = e ∧ b ≠ c then v
          else if b = e ∧ c = d ∧ b ≠ c then v
          else 0) := by
          simp [hquad]
    _ =
        (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
          if b = c ∧ b = d ∧ b = e then μ4 else 0) +
        (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
          if b = c ∧ d = e ∧ b ≠ d then v else 0) +
        (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
          if b = d ∧ c = e ∧ b ≠ c then v else 0) +
        (∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ e ∈ s,
          if b = e ∧ c = d ∧ b ≠ c then v else 0) := by
          simp [hsplit, Finset.sum_add_distrib]
    _ = ((Fintype.card κ : ℝ) - 1) * empiricalCentralMoment Y 4 +
        3 * ((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 2) *
          empiricalCumulant2 Y ^ 2 := by
          rw [sum_finset_allEqual4_eq_card_mul]
          rw [sum_finset_pairPattern_eq_card_mul_card_sub_one_mul]
          rw [sum_finset_pairPattern_ac_bd_eq_card_mul_card_sub_one_mul]
          rw [sum_finset_pairPattern_ad_bc_eq_card_mul_card_sub_one_mul]
          rw [hscard]
          dsimp [μ4, v]
          ring

/-- A selected centered ordinary-bootstrap coordinate is independent of the
centered sum over all other coordinates. -/
private theorem indepFun_centered_uniformOn_fun_eval_sum_erase
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) (a : κ) :
    IndepFun
      (fun ωs : κ → ι => Y (ωs a) - empiricalMean Y)
      (fun ωs : κ → ι =>
        ∑ t : {t // t ∈ Finset.univ.erase a}, (Y (ωs t.1) - empiricalMean Y))
      (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  let A : Finset κ := {a}
  let B : Finset κ := Finset.univ.erase a
  have hIndep : iIndepFun X Pκ := by
    simpa [X, Pκ] using
      (iIndepFun_uniformOn_fun_eval_sub_empiricalMean
        (κ := κ) (ι := ι) (E := ℝ) Y)
  have hMeas : ∀ t : κ, Measurable (X t) := fun t =>
    measurable_of_finite (X t)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxa : x = a := by
      simpa [A] using hxA
    subst x
    simp [B] at hxB
  let φ : (A → ℝ) → ℝ := fun z => z ⟨a, by simp [A]⟩
  let ψ : (B → ℝ) → ℝ := fun z => ∑ t : B, z t
  have hφ : Measurable φ := by
    dsimp [φ]
    exact measurable_pi_apply (X := fun _ : A => ℝ) (⟨a, by simp [A]⟩ : A)
  have hψ : Measurable ψ := by
    dsimp [ψ]
    exact Finset.measurable_fun_sum Finset.univ
      (fun t _ht => measurable_pi_apply (X := fun _ : B => ℝ) t)
  refine IndepFun.congr ((hIndep.indepFun_finset A B hAB hMeas).comp hφ hψ) ?_ ?_
  · filter_upwards with ωs
    simp [φ, A, X]
  · filter_upwards with ωs
    dsimp [ψ, X, B, Function.comp_def]

/-- Cube of the centered ordinary-bootstrap sum.

This is the finite iid expansion behind the third-moment line in Hansen
equation (10.14), before applying the `sqrt (#κ)` normalization. -/
theorem integral_cube_centered_uniformOn_fun_sum_eq_card_mul_empiricalCumulant3
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι, (∑ t : κ, (Y (ωs t) - empiricalMean Y)) ^ 3
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      (Fintype.card κ : ℝ) * empiricalCumulant3 Y := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  have hcube : ∀ ωs : κ → ι,
      (∑ t : κ, X t ωs) ^ 3 =
        ∑ a : κ, ∑ b : κ, ∑ c : κ, X a ωs * X b ωs * X c ωs := by
    intro ωs
    simp [pow_succ, Finset.mul_sum, mul_comm]
  have htriple : ∀ a b c : κ,
      ∫ ωs, X a ωs * X b ωs * X c ωs ∂Pκ =
        if a = b ∧ a = c then empiricalCumulant3 Y else 0 := by
    intro a b c
    simpa [X, Pκ] using
      (integral_mul_mul_uniformOn_fun_eval_sub_empiricalMean_eq
        (κ := κ) (Y := Y) a b c)
  have hinner : ∀ a : κ,
      (∑ b : κ, ∑ c : κ,
          (if a = b ∧ a = c then empiricalCumulant3 Y else 0)) =
        empiricalCumulant3 Y := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · simp
      · intro c _hc_mem hc
        have hca : a ≠ c := fun h => hc h.symm
        simp [hca]
      · intro ha
        exact (ha (Finset.mem_univ a)).elim
    · intro b _hb_mem hb
      have hab : a ≠ b := fun h => hb h.symm
      simp [hab]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  calc
    ∫ ωs : κ → ι, (∑ t : κ, (Y (ωs t) - empiricalMean Y)) ^ 3 ∂Pκ =
        ∫ ωs : κ → ι, ∑ a : κ, ∑ b : κ, ∑ c : κ,
          X a ωs * X b ωs * X c ωs ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          simpa [X] using hcube ωs
    _ = ∑ a : κ, ∑ b : κ, ∑ c : κ,
          ∫ ωs : κ → ι, X a ωs * X b ωs * X c ωs ∂Pκ := by
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun a ωs => ∑ b : κ, ∑ c : κ,
              X a ωs * X b ωs * X c ωs)
            (μ := Pκ)
            (hf := by
              intro a _ha
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun b ωs => ∑ c : κ, X a ωs * X b ωs * X c ωs)
                (fun b _hb =>
                  integrable_finset_sum (s := Finset.univ)
                    (f := fun c ωs => X a ωs * X b ωs * X c ωs)
                    (fun c _hc => Integrable.of_finite)))]
          congr with a
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun b ωs => ∑ c : κ, X a ωs * X b ωs * X c ωs)
            (μ := Pκ)
            (hf := by
              intro b _hb
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun c ωs => X a ωs * X b ωs * X c ωs)
                (fun c _hc => Integrable.of_finite))]
          congr with b
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun c ωs => X a ωs * X b ωs * X c ωs)
            (μ := Pκ)
            (hf := by
              intro c _hc
              exact Integrable.of_finite)]
    _ = ∑ a : κ, ∑ b : κ, ∑ c : κ,
          (if a = b ∧ a = c then empiricalCumulant3 Y else 0) := by
          simp [htriple]
    _ = (Fintype.card κ : ℝ) * empiricalCumulant3 Y := by
          simp [hinner]

/-- Fourth power of the centered ordinary-bootstrap sum.

This is the finite iid expansion behind the fourth-moment line in Hansen
equation (10.14), before applying the `sqrt (#κ)` normalization. -/
theorem integral_fourth_centered_uniformOn_fun_sum_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι, (∑ t : κ, (Y (ωs t) - empiricalMean Y)) ^ 4
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      (Fintype.card κ : ℝ) * empiricalCentralMoment Y 4 +
        3 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          empiricalCumulant2 Y ^ 2 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  let μ4 : ℝ := empiricalCentralMoment Y 4
  let v : ℝ := empiricalCumulant2 Y ^ 2
  have hfour : ∀ ωs : κ → ι,
      (∑ t : κ, X t ωs) ^ 4 =
        ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          X a ωs * X b ωs * X c ωs * X d ωs := by
    intro ωs
    simp [pow_succ, Finset.mul_sum, mul_assoc, mul_comm]
  have hquad : ∀ a b c d : κ,
      ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ =
        if a = b ∧ a = c ∧ a = d then μ4
        else if a = b ∧ c = d ∧ a ≠ c then v
        else if a = c ∧ b = d ∧ a ≠ b then v
        else if a = d ∧ b = c ∧ a ≠ b then v
        else 0 := by
    intro a b c d
    simpa [X, Pκ, μ4, v] using
      (integral_mul_mul_mul_uniformOn_fun_eval_sub_empiricalMean_eq
        (κ := κ) (Y := Y) a b c d)
  have hsplit : ∀ a b c d : κ,
      (if a = b ∧ a = c ∧ a = d then μ4
        else if a = b ∧ c = d ∧ a ≠ c then v
        else if a = c ∧ b = d ∧ a ≠ b then v
        else if a = d ∧ b = c ∧ a ≠ b then v
        else 0) =
        (if a = b ∧ a = c ∧ a = d then μ4 else 0) +
          (if a = b ∧ c = d ∧ a ≠ c then v else 0) +
          (if a = c ∧ b = d ∧ a ≠ b then v else 0) +
          (if a = d ∧ b = c ∧ a ≠ b then v else 0) := by
    intro a b c d
    by_cases hAll : a = b ∧ a = c ∧ a = d
    · rcases hAll with ⟨hab, hac, had⟩
      subst b
      subst c
      subst d
      simp
    · by_cases hABCD : a = b ∧ c = d ∧ a ≠ c
      · rcases hABCD with ⟨hab, hcd, hac⟩
        subst b
        subst d
        simp [hac]
      · by_cases hACBD : a = c ∧ b = d ∧ a ≠ b
        · rcases hACBD with ⟨hac, hbd, hab⟩
          subst c
          subst d
          simp [hab]
        · by_cases hADBC : a = d ∧ b = c ∧ a ≠ b
          · rcases hADBC with ⟨had, hbc, hab⟩
            subst d
            subst c
            simp [hab]
          · simp [hAll, hABCD, hACBD, hADBC]
  calc
    ∫ ωs : κ → ι, (∑ t : κ, (Y (ωs t) - empiricalMean Y)) ^ 4 ∂Pκ =
        ∫ ωs : κ → ι, ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          simpa [X] using hfour ωs
    _ = ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          ∫ ωs : κ → ι, X a ωs * X b ωs * X c ωs * X d ωs ∂Pκ := by
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun a ωs => ∑ b : κ, ∑ c : κ, ∑ d : κ,
              X a ωs * X b ωs * X c ωs * X d ωs)
            (μ := Pκ)
            (hf := by
              intro a _ha
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun b ωs => ∑ c : κ, ∑ d : κ,
                  X a ωs * X b ωs * X c ωs * X d ωs)
                (fun b _hb =>
                  integrable_finset_sum (s := Finset.univ)
                    (f := fun c ωs => ∑ d : κ,
                      X a ωs * X b ωs * X c ωs * X d ωs)
                    (fun c _hc =>
                      integrable_finset_sum (s := Finset.univ)
                        (f := fun d ωs => X a ωs * X b ωs * X c ωs * X d ωs)
                        (fun d _hd => Integrable.of_finite))))]
          congr with a
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun b ωs => ∑ c : κ, ∑ d : κ,
              X a ωs * X b ωs * X c ωs * X d ωs)
            (μ := Pκ)
            (hf := by
              intro b _hb
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun c ωs => ∑ d : κ,
                  X a ωs * X b ωs * X c ωs * X d ωs)
                (fun c _hc =>
                  integrable_finset_sum (s := Finset.univ)
                    (f := fun d ωs => X a ωs * X b ωs * X c ωs * X d ωs)
                    (fun d _hd => Integrable.of_finite)))]
          congr with b
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun c ωs => ∑ d : κ,
              X a ωs * X b ωs * X c ωs * X d ωs)
            (μ := Pκ)
            (hf := by
              intro c _hc
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun d ωs => X a ωs * X b ωs * X c ωs * X d ωs)
                (fun d _hd => Integrable.of_finite))]
          congr with c
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun d ωs => X a ωs * X b ωs * X c ωs * X d ωs)
            (μ := Pκ)
            (hf := by
              intro d _hd
              exact Integrable.of_finite)]
    _ = ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          (if a = b ∧ a = c ∧ a = d then μ4
          else if a = b ∧ c = d ∧ a ≠ c then v
          else if a = c ∧ b = d ∧ a ≠ b then v
          else if a = d ∧ b = c ∧ a ≠ b then v
          else 0) := by
          simp [hquad]
    _ =
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          if a = b ∧ a = c ∧ a = d then μ4 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          if a = b ∧ c = d ∧ a ≠ c then v else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          if a = c ∧ b = d ∧ a ≠ b then v else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          if a = d ∧ b = c ∧ a ≠ b then v else 0) := by
          simp [hsplit, Finset.sum_add_distrib]
    _ = (Fintype.card κ : ℝ) * empiricalCentralMoment Y 4 +
        3 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          empiricalCumulant2 Y ^ 2 := by
          rw [sum_allEqual4_eq_card_mul]
          rw [sum_pairPattern_eq_card_mul_card_sub_one_mul]
          rw [sum_pairPattern_ac_bd_eq_card_mul_card_sub_one_mul]
          rw [sum_pairPattern_ad_bc_eq_card_mul_card_sub_one_mul]
          simp [μ4, v]
          ring

/-- Fifth power of the centered ordinary-bootstrap sum.

This is the finite iid expansion behind the fifth-moment line in Hansen
equation (10.14), before applying the `sqrt (#κ)` normalization. -/
theorem integral_fifth_centered_uniformOn_fun_sum_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι, (∑ t : κ, (Y (ωs t) - empiricalMean Y)) ^ 5
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      (Fintype.card κ : ℝ) * empiricalCentralMoment Y 5 +
        10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          empiricalCumulant3 Y * empiricalCumulant2 Y := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  let μ5 : ℝ := empiricalCentralMoment Y 5
  let m32 : ℝ := empiricalCumulant3 Y * empiricalCumulant2 Y
  have hfifth : ∀ ωs : κ → ι,
      (∑ t : κ, X t ωs) ^ 5 =
        ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          X a ωs * X b ωs * X c ωs * X d ωs * X e ωs := by
    intro ωs
    simp [pow_succ, Finset.mul_sum, mul_assoc, mul_comm]
  have hquint : ∀ a b c d e : κ,
      ∫ ωs, X a ωs * X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ =
        (if a = b ∧ a = c ∧ a = d ∧ a = e then μ5 else 0) +
        (if a = b ∧ a = c ∧ d = e ∧ a ≠ d then m32 else 0) +
        (if a = b ∧ a = d ∧ c = e ∧ a ≠ c then m32 else 0) +
        (if a = b ∧ a = e ∧ c = d ∧ a ≠ c then m32 else 0) +
        (if a = c ∧ a = d ∧ b = e ∧ a ≠ b then m32 else 0) +
        (if a = c ∧ a = e ∧ b = d ∧ a ≠ b then m32 else 0) +
        (if a = d ∧ a = e ∧ b = c ∧ a ≠ b then m32 else 0) +
        (if b = c ∧ b = d ∧ a = e ∧ b ≠ a then m32 else 0) +
        (if b = c ∧ b = e ∧ a = d ∧ b ≠ a then m32 else 0) +
        (if b = d ∧ b = e ∧ a = c ∧ b ≠ a then m32 else 0) +
        (if c = d ∧ c = e ∧ a = b ∧ c ≠ a then m32 else 0) := by
    intro a b c d e
    simpa [X, Pκ, μ5, m32] using
      (integral_mul_mul_mul_mul_uniformOn_fun_eval_sub_empiricalMean_eq
        (κ := κ) (Y := Y) a b c d e)
  calc
    ∫ ωs : κ → ι, (∑ t : κ, (Y (ωs t) - empiricalMean Y)) ^ 5 ∂Pκ =
        ∫ ωs : κ → ι, ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          X a ωs * X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          simpa [X] using hfifth ωs
    _ = ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          ∫ ωs : κ → ι, X a ωs * X b ωs * X c ωs * X d ωs * X e ωs ∂Pκ := by
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun a ωs => ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
              X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro a _ha
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun b ωs => ∑ c : κ, ∑ d : κ, ∑ e : κ,
                  X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                (fun b _hb =>
                  integrable_finset_sum (s := Finset.univ)
                    (f := fun c ωs => ∑ d : κ, ∑ e : κ,
                      X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                    (fun c _hc =>
                      integrable_finset_sum (s := Finset.univ)
                        (f := fun d ωs => ∑ e : κ,
                          X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                        (fun d _hd =>
                          integrable_finset_sum (s := Finset.univ)
                            (f := fun e ωs =>
                              X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                            (fun e _he => Integrable.of_finite)))))]
          congr with a
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun b ωs => ∑ c : κ, ∑ d : κ, ∑ e : κ,
              X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro b _hb
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun c ωs => ∑ d : κ, ∑ e : κ,
                  X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                (fun c _hc =>
                  integrable_finset_sum (s := Finset.univ)
                    (f := fun d ωs => ∑ e : κ,
                      X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                    (fun d _hd =>
                      integrable_finset_sum (s := Finset.univ)
                        (f := fun e ωs =>
                          X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                        (fun e _he => Integrable.of_finite))))]
          congr with b
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun c ωs => ∑ d : κ, ∑ e : κ,
              X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro c _hc
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun d ωs => ∑ e : κ,
                  X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                (fun d _hd =>
                  integrable_finset_sum (s := Finset.univ)
                    (f := fun e ωs =>
                      X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                    (fun e _he => Integrable.of_finite)))]
          congr with c
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun d ωs => ∑ e : κ,
              X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro d _hd
              exact integrable_finset_sum (s := Finset.univ)
                (f := fun e ωs =>
                  X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
                (fun e _he => Integrable.of_finite))]
          congr with d
          rw [integral_finset_sum (s := Finset.univ)
            (f := fun e ωs =>
              X a ωs * X b ωs * X c ωs * X d ωs * X e ωs)
            (μ := Pκ)
            (hf := by
              intro e _he
              exact Integrable.of_finite)]
    _ = ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          ((if a = b ∧ a = c ∧ a = d ∧ a = e then μ5 else 0) +
          (if a = b ∧ a = c ∧ d = e ∧ a ≠ d then m32 else 0) +
          (if a = b ∧ a = d ∧ c = e ∧ a ≠ c then m32 else 0) +
          (if a = b ∧ a = e ∧ c = d ∧ a ≠ c then m32 else 0) +
          (if a = c ∧ a = d ∧ b = e ∧ a ≠ b then m32 else 0) +
          (if a = c ∧ a = e ∧ b = d ∧ a ≠ b then m32 else 0) +
          (if a = d ∧ a = e ∧ b = c ∧ a ≠ b then m32 else 0) +
          (if b = c ∧ b = d ∧ a = e ∧ b ≠ a then m32 else 0) +
          (if b = c ∧ b = e ∧ a = d ∧ b ≠ a then m32 else 0) +
          (if b = d ∧ b = e ∧ a = c ∧ b ≠ a then m32 else 0) +
          (if c = d ∧ c = e ∧ a = b ∧ c ≠ a then m32 else 0)) := by
          simp [hquint]
    _ =
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if a = b ∧ a = c ∧ a = d ∧ a = e then μ5 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if a = b ∧ a = c ∧ d = e ∧ a ≠ d then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if a = b ∧ a = d ∧ c = e ∧ a ≠ c then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if a = b ∧ a = e ∧ c = d ∧ a ≠ c then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if a = c ∧ a = d ∧ b = e ∧ a ≠ b then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if a = c ∧ a = e ∧ b = d ∧ a ≠ b then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if a = d ∧ a = e ∧ b = c ∧ a ≠ b then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if b = c ∧ b = d ∧ a = e ∧ b ≠ a then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if b = c ∧ b = e ∧ a = d ∧ b ≠ a then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if b = d ∧ b = e ∧ a = c ∧ b ≠ a then m32 else 0) +
        (∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ, ∑ e : κ,
          if c = d ∧ c = e ∧ a = b ∧ c ≠ a then m32 else 0) := by
          simp only [Finset.sum_add_distrib, add_assoc]
    _ = (Fintype.card κ : ℝ) * empiricalCentralMoment Y 5 +
        10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          empiricalCumulant3 Y * empiricalCumulant2 Y := by
          simp only [
            sum_allEqual5_eq_card_mul,
            sum_triplePairPattern_abc_de_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_abd_ce_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_abe_cd_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_acd_be_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_ace_bd_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_ade_bc_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_bcd_ae_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_bce_ad_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_bde_ac_eq_card_mul_card_sub_one_mul,
            sum_triplePairPattern_cde_ab_eq_card_mul_card_sub_one_mul]
          dsimp [μ5, m32]
          ring

/-- Sixth power of the centered ordinary-bootstrap sum.

This is the finite iid expansion behind the sixth-moment line in Hansen
equation (10.14), before applying the `sqrt (#κ)` normalization. The proof
uses the decomposition of the full centered sum into one selected coordinate
plus the centered sum over all other bootstrap coordinates. -/
theorem integral_sixth_centered_uniformOn_fun_sum_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι, (∑ t : κ, (Y (ωs t) - empiricalMean Y)) ^ 6
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      (Fintype.card κ : ℝ) * empiricalCentralMoment Y 6 +
        15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          empiricalCentralMoment Y 4 * empiricalCumulant2 Y +
        10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          empiricalCumulant3 Y ^ 2 +
        15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          ((Fintype.card κ : ℝ) - 2) * empiricalCumulant2 Y ^ 3 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : κ → (κ → ι) → ℝ :=
    fun t ωs => Y (ωs t) - empiricalMean Y
  let S : (κ → ι) → ℝ := fun ωs => ∑ t : κ, X t ωs
  let T : κ → (κ → ι) → ℝ :=
    fun a ωs => ∑ t : {t // t ∈ Finset.univ.erase a}, X t.1 ωs
  let n : ℝ := Fintype.card κ
  let μ2 : ℝ := empiricalCumulant2 Y
  let μ3 : ℝ := empiricalCumulant3 Y
  let μ4 : ℝ := empiricalCentralMoment Y 4
  let μ6 : ℝ := empiricalCentralMoment Y 6
  have hT_finset : ∀ a : κ, ∀ ωs : κ → ι,
      T a ωs = ∑ t ∈ Finset.univ.erase a, X t ωs := by
    intro a ωs
    simpa [T] using
      (Finset.sum_coe_sort (s := Finset.univ.erase a) (f := fun t => X t ωs))
  have hSsplit : ∀ a : κ, ∀ ωs : κ → ι, S ωs = X a ωs + T a ωs := by
    intro a ωs
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset κ)) (a := a)
      (f := fun t => X t ωs) (Finset.mem_univ a)
    calc
      S ωs = ∑ t : κ, X t ωs := rfl
      _ = X a ωs + ∑ t ∈ Finset.univ.erase a, X t ωs := by
          rw [h.symm]
          rw [add_comm]
      _ = X a ωs + T a ωs := by
          rw [(hT_finset a ωs).symm]
  have hXmean : ∀ a : κ, ∫ ωs, X a ωs ∂Pκ = 0 := by
    intro a
    have hbase :
        ∫ ωs : κ → ι, Y (ωs a) ∂Pκ = empiricalMean Y := by
      simpa [Pκ] using
        (integral_uniformOn_fun_eval_eq_empiricalMean
          (κ := κ) (Y := Y) a)
    have hInt : Integrable (fun ωs : κ → ι => Y (ωs a)) Pκ :=
      Integrable.of_finite
    calc
      ∫ ωs, X a ωs ∂Pκ =
          ∫ ωs : κ → ι, Y (ωs a) - empiricalMean Y ∂Pκ := rfl
      _ = ∫ ωs : κ → ι, Y (ωs a) ∂Pκ -
            ∫ _ωs : κ → ι, empiricalMean Y ∂Pκ := by
          rw [integral_sub hInt (integrable_const _)]
      _ = 0 := by
          rw [hbase]
          simp [Pκ]
  have hX2 : ∀ a : κ, ∫ ωs, X a ωs ^ 2 ∂Pκ = μ2 := by
    intro a
    change
      ∫ ωs : κ → ι, (Y (ωs a) - empiricalMean Y) ^ 2
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        μ2
    simpa [μ2] using
      integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) a 2
  have hX3 : ∀ a : κ, ∫ ωs, X a ωs ^ 3 ∂Pκ = μ3 := by
    intro a
    change
      ∫ ωs : κ → ι, (Y (ωs a) - empiricalMean Y) ^ 3
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        μ3
    simpa [μ3, empiricalCentralMoment_three_eq_cumulant3] using
      integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) a 3
  have hX4 : ∀ a : κ, ∫ ωs, X a ωs ^ 4 ∂Pκ = μ4 := by
    intro a
    change
      ∫ ωs : κ → ι, (Y (ωs a) - empiricalMean Y) ^ 4
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        μ4
    exact
      integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) a 4
  have hX6 : ∀ a : κ, ∫ ωs, X a ωs ^ 6 ∂Pκ = μ6 := by
    intro a
    change
      ∫ ωs : κ → ι, (Y (ωs a) - empiricalMean Y) ^ 6
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
        μ6
    exact
      integral_pow_uniformOn_fun_eval_sub_empiricalMean_eq_empiricalCentralMoment
        (κ := κ) (Y := Y) a 6
  have hTmean : ∀ a : κ, ∫ ωs, T a ωs ∂Pκ = 0 := by
    intro a
    calc
      ∫ ωs, T a ωs ∂Pκ =
          ∫ ωs : κ → ι, ∑ t : {t // t ∈ Finset.univ.erase a}, X t.1 ωs ∂Pκ := rfl
      _ = ∑ t : {t // t ∈ Finset.univ.erase a}, ∫ ωs : κ → ι, X t.1 ωs ∂Pκ := by
          rw [integral_finset_sum
            (s := (Finset.univ : Finset {t // t ∈ Finset.univ.erase a}))
            (f := fun t ωs => X t.1 ωs)
            (μ := Pκ)
            (hf := by
              intro t _ht
              exact Integrable.of_finite)]
      _ = 0 := by
          simp [hXmean]
  have hT2 : ∀ a : κ, ∫ ωs, T a ωs ^ 2 ∂Pκ = (n - 1) * μ2 := by
    intro a
    calc
      ∫ ωs, T a ωs ^ 2 ∂Pκ =
          ∫ ωs : κ → ι, (∑ t ∈ Finset.univ.erase a, X t ωs) ^ 2 ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hT_finset a ωs]
      _ = (n - 1) * μ2 := by
          simpa [X, Pκ, n, μ2] using
            integral_sq_centered_uniformOn_fun_sum_erase_eq
              (κ := κ) (Y := Y) a
  have hT3 : ∀ a : κ, ∫ ωs, T a ωs ^ 3 ∂Pκ = (n - 1) * μ3 := by
    intro a
    calc
      ∫ ωs, T a ωs ^ 3 ∂Pκ =
          ∫ ωs : κ → ι, (∑ t ∈ Finset.univ.erase a, X t ωs) ^ 3 ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hT_finset a ωs]
      _ = (n - 1) * μ3 := by
          simpa [X, Pκ, n, μ3] using
            integral_cube_centered_uniformOn_fun_sum_erase_eq
              (κ := κ) (Y := Y) a
  have hT4 : ∀ a : κ,
      ∫ ωs, T a ωs ^ 4 ∂Pκ =
        (n - 1) * μ4 + 3 * (n - 1) * (n - 2) * μ2 ^ 2 := by
    intro a
    calc
      ∫ ωs, T a ωs ^ 4 ∂Pκ =
          ∫ ωs : κ → ι, (∑ t ∈ Finset.univ.erase a, X t ωs) ^ 4 ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hT_finset a ωs]
      _ = (n - 1) * μ4 + 3 * (n - 1) * (n - 2) * μ2 ^ 2 := by
          simpa [X, Pκ, n, μ2, μ4] using
            integral_fourth_centered_uniformOn_fun_sum_erase_eq
              (κ := κ) (Y := Y) a
  have hIndepXT : ∀ a : κ, IndepFun (X a) (T a) Pκ := by
    intro a
    simpa [X, T, Pκ] using
      indepFun_centered_uniformOn_fun_eval_sum_erase
        (κ := κ) (Y := Y) a
  have hfactor : ∀ a : κ, ∀ r q : ℕ,
      ∫ ωs, X a ωs ^ r * T a ωs ^ q ∂Pκ =
        (∫ ωs, X a ωs ^ r ∂Pκ) * ∫ ωs, T a ωs ^ q ∂Pκ := by
    intro a r q
    have hind :
        IndepFun (fun ωs : κ → ι => X a ωs ^ r)
          (fun ωs : κ → ι => T a ωs ^ q) Pκ :=
      (hIndepXT a).comp (measurable_id.pow_const r) (measurable_id.pow_const q)
    exact hind.integral_mul_eq_mul_integral
      (measurable_of_finite (fun ωs : κ → ι => X a ωs ^ r)).aestronglyMeasurable
      (measurable_of_finite (fun ωs : κ → ι => T a ωs ^ q)).aestronglyMeasurable
  have hcontrib : ∀ a : κ,
      ∫ ωs, X a ωs * S ωs ^ 5 ∂Pκ =
        μ6 + 15 * (n - 1) * μ4 * μ2 +
          10 * (n - 1) * μ3 ^ 2 +
          15 * (n - 1) * (n - 2) * μ2 ^ 3 := by
    intro a
    have h51 :
        ∫ ωs, X a ωs ^ 5 * T a ωs ∂Pκ = 0 := by
      calc
        ∫ ωs, X a ωs ^ 5 * T a ωs ∂Pκ =
            ∫ ωs, X a ωs ^ 5 * T a ωs ^ 1 ∂Pκ := by
            simp
        _ = (∫ ωs, X a ωs ^ 5 ∂Pκ) * ∫ ωs, T a ωs ^ 1 ∂Pκ :=
            hfactor a 5 1
        _ = 0 := by
            rw [show (∫ ωs, T a ωs ^ 1 ∂Pκ) = 0 by simpa using hTmean a]
            ring
    have h42 :
        ∫ ωs, X a ωs ^ 4 * T a ωs ^ 2 ∂Pκ =
          μ4 * ((n - 1) * μ2) := by
      calc
        ∫ ωs, X a ωs ^ 4 * T a ωs ^ 2 ∂Pκ =
            (∫ ωs, X a ωs ^ 4 ∂Pκ) * ∫ ωs, T a ωs ^ 2 ∂Pκ :=
            hfactor a 4 2
        _ = μ4 * ((n - 1) * μ2) := by
            rw [hX4 a, hT2 a]
    have h33 :
        ∫ ωs, X a ωs ^ 3 * T a ωs ^ 3 ∂Pκ =
          μ3 * ((n - 1) * μ3) := by
      calc
        ∫ ωs, X a ωs ^ 3 * T a ωs ^ 3 ∂Pκ =
            (∫ ωs, X a ωs ^ 3 ∂Pκ) * ∫ ωs, T a ωs ^ 3 ∂Pκ :=
            hfactor a 3 3
        _ = μ3 * ((n - 1) * μ3) := by
            rw [hX3 a, hT3 a]
    have h24 :
        ∫ ωs, X a ωs ^ 2 * T a ωs ^ 4 ∂Pκ =
          μ2 * ((n - 1) * μ4 + 3 * (n - 1) * (n - 2) * μ2 ^ 2) := by
      calc
        ∫ ωs, X a ωs ^ 2 * T a ωs ^ 4 ∂Pκ =
            (∫ ωs, X a ωs ^ 2 ∂Pκ) * ∫ ωs, T a ωs ^ 4 ∂Pκ :=
            hfactor a 2 4
        _ = μ2 * ((n - 1) * μ4 + 3 * (n - 1) * (n - 2) * μ2 ^ 2) := by
            rw [hX2 a, hT4 a]
    have h15 :
        ∫ ωs, X a ωs * T a ωs ^ 5 ∂Pκ = 0 := by
      calc
        ∫ ωs, X a ωs * T a ωs ^ 5 ∂Pκ =
            ∫ ωs, X a ωs ^ 1 * T a ωs ^ 5 ∂Pκ := by
            simp
        _ = (∫ ωs, X a ωs ^ 1 ∂Pκ) * ∫ ωs, T a ωs ^ 5 ∂Pκ :=
            hfactor a 1 5
        _ = 0 := by
            rw [show (∫ ωs, X a ωs ^ 1 ∂Pκ) = 0 by simpa using hXmean a]
            ring
    have hpoly : ∀ ωs : κ → ι,
        X a ωs * S ωs ^ 5 =
          X a ωs ^ 6 +
            5 * (X a ωs ^ 5 * T a ωs) +
            10 * (X a ωs ^ 4 * T a ωs ^ 2) +
            10 * (X a ωs ^ 3 * T a ωs ^ 3) +
            5 * (X a ωs ^ 2 * T a ωs ^ 4) +
            X a ωs * T a ωs ^ 5 := by
      intro ωs
      rw [hSsplit a ωs]
      ring
    calc
      ∫ ωs, X a ωs * S ωs ^ 5 ∂Pκ =
          ∫ ωs,
            X a ωs ^ 6 +
              5 * (X a ωs ^ 5 * T a ωs) +
              10 * (X a ωs ^ 4 * T a ωs ^ 2) +
              10 * (X a ωs ^ 3 * T a ωs ^ 3) +
              5 * (X a ωs ^ 2 * T a ωs ^ 4) +
              X a ωs * T a ωs ^ 5 ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          exact hpoly ωs
      _ =
          ∫ ωs, X a ωs ^ 6 ∂Pκ +
            5 * ∫ ωs, X a ωs ^ 5 * T a ωs ∂Pκ +
            10 * ∫ ωs, X a ωs ^ 4 * T a ωs ^ 2 ∂Pκ +
            10 * ∫ ωs, X a ωs ^ 3 * T a ωs ^ 3 ∂Pκ +
            5 * ∫ ωs, X a ωs ^ 2 * T a ωs ^ 4 ∂Pκ +
            ∫ ωs, X a ωs * T a ωs ^ 5 ∂Pκ := by
          simp [integral_add, integral_const_mul]
      _ = μ6 + 15 * (n - 1) * μ4 * μ2 +
          10 * (n - 1) * μ3 ^ 2 +
          15 * (n - 1) * (n - 2) * μ2 ^ 3 := by
          rw [hX6 a, h51, h42, h33, h24, h15]
          ring
  have hsix : ∀ ωs : κ → ι,
      S ωs ^ 6 = ∑ a : κ, X a ωs * S ωs ^ 5 := by
    intro ωs
    calc
      S ωs ^ 6 = S ωs * S ωs ^ 5 := by
          ring
      _ = (∑ a : κ, X a ωs) * S ωs ^ 5 := rfl
      _ = ∑ a : κ, X a ωs * S ωs ^ 5 := by
          rw [Finset.sum_mul]
  calc
    ∫ ωs : κ → ι, (∑ t : κ, (Y (ωs t) - empiricalMean Y)) ^ 6 ∂Pκ =
        ∫ ωs : κ → ι, S ωs ^ 6 ∂Pκ := by
        simp [S, X]
    _ = ∫ ωs : κ → ι, ∑ a : κ, X a ωs * S ωs ^ 5 ∂Pκ := by
        refine integral_congr_ae ?_
        filter_upwards with ωs
        rw [hsix ωs]
    _ = ∑ a : κ, ∫ ωs : κ → ι, X a ωs * S ωs ^ 5 ∂Pκ := by
        rw [integral_finset_sum (s := Finset.univ)
          (f := fun a ωs => X a ωs * S ωs ^ 5)
          (μ := Pκ)
          (hf := by
            intro a _ha
            exact Integrable.of_finite)]
    _ = ∑ _a : κ,
          (μ6 + 15 * (n - 1) * μ4 * μ2 +
            10 * (n - 1) * μ3 ^ 2 +
            15 * (n - 1) * (n - 2) * μ2 ^ 3) := by
        simp [hcontrib]
    _ = (Fintype.card κ : ℝ) * empiricalCentralMoment Y 6 +
        15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          empiricalCentralMoment Y 4 * empiricalCumulant2 Y +
        10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          empiricalCumulant3 Y ^ 2 +
        15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
          ((Fintype.card κ : ℝ) - 2) * empiricalCumulant2 Y ^ 3 := by
        simp [n, μ2, μ3, μ4, μ6]
        ring

/-- Hansen equation (10.14), third conditional moment of the normalized
ordinary-bootstrap sample mean. -/
theorem integral_cube_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 3
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalCumulant3 Y / Real.sqrt (Fintype.card κ : ℝ) := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let c : ℝ := (Real.sqrt (Fintype.card κ : ℝ))⁻¹
  let S : (κ → ι) → ℝ :=
    fun ωs => ∑ t : κ, (Y (ωs t) - empiricalMean Y)
  have hpoint : ∀ ωs : κ → ι,
      Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y) =
        c * S ωs := by
    intro ωs
    simpa [c, S] using
      normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_sum
        (κ := κ) (Y := Y) ωs
  have hsum :
      ∫ ωs : κ → ι, S ωs ^ 3 ∂Pκ =
        (Fintype.card κ : ℝ) * empiricalCumulant3 Y := by
    simpa [S, Pκ] using
      integral_cube_centered_uniformOn_fun_sum_eq_card_mul_empiricalCumulant3
        (κ := κ) (Y := Y)
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_ne : Real.sqrt (Fintype.card κ : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hcard_pos).ne'
  have hsqrt_sq :
      Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
    Real.sq_sqrt hcard_pos.le
  have hcoef :
      c ^ 3 * (Fintype.card κ : ℝ) =
        (Real.sqrt (Fintype.card κ : ℝ))⁻¹ := by
    calc
      c ^ 3 * (Fintype.card κ : ℝ) =
          (Real.sqrt (Fintype.card κ : ℝ))⁻¹ ^ 3 *
            Real.sqrt (Fintype.card κ : ℝ) ^ 2 := by
            dsimp [c]
            rw [hsqrt_sq]
      _ = (Real.sqrt (Fintype.card κ : ℝ))⁻¹ := by
            field_simp [hsqrt_ne]
  calc
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 3 ∂Pκ =
        ∫ ωs : κ → ι, (c * S ωs) ^ 3 ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hpoint ωs]
    _ = c ^ 3 * ∫ ωs : κ → ι, S ωs ^ 3 ∂Pκ := by
          simp [mul_pow, integral_const_mul]
    _ = c ^ 3 * ((Fintype.card κ : ℝ) * empiricalCumulant3 Y) := by
          rw [hsum]
    _ = empiricalCumulant3 Y / Real.sqrt (Fintype.card κ : ℝ) := by
          rw [← mul_assoc, hcoef]
          rw [div_eq_mul_inv]
          ring

/-- Hansen equation (10.14), fourth conditional moment of the normalized
ordinary-bootstrap sample mean, before rewriting the fourth central moment as a
sample cumulant. -/
theorem integral_fourth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 4
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalCentralMoment Y 4 / (Fintype.card κ : ℝ) +
        3 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) *
          empiricalCumulant2 Y ^ 2 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let c : ℝ := (Real.sqrt (Fintype.card κ : ℝ))⁻¹
  let S : (κ → ι) → ℝ :=
    fun ωs => ∑ t : κ, (Y (ωs t) - empiricalMean Y)
  let μ4 : ℝ := empiricalCentralMoment Y 4
  let v : ℝ := empiricalCumulant2 Y ^ 2
  have hpoint : ∀ ωs : κ → ι,
      Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y) =
        c * S ωs := by
    intro ωs
    simpa [c, S] using
      normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_sum
        (κ := κ) (Y := Y) ωs
  have hsum :
      ∫ ωs : κ → ι, S ωs ^ 4 ∂Pκ =
        (Fintype.card κ : ℝ) * μ4 +
          3 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * v := by
    simpa [S, Pκ, μ4, v] using
      integral_fourth_centered_uniformOn_fun_sum_eq
        (κ := κ) (Y := Y)
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_ne : Real.sqrt (Fintype.card κ : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hcard_pos).ne'
  have hsqrt_sq :
      Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
    Real.sq_sqrt hcard_pos.le
  have hc4 : c ^ 4 = ((Fintype.card κ : ℝ) ^ 2)⁻¹ := by
    calc
      c ^ 4 = ((Real.sqrt (Fintype.card κ : ℝ))⁻¹) ^ 4 := rfl
      _ = (Real.sqrt (Fintype.card κ : ℝ) ^ 4)⁻¹ := by
          rw [inv_pow]
      _ = ((Fintype.card κ : ℝ) ^ 2)⁻¹ := by
          congr 1
          calc
            Real.sqrt (Fintype.card κ : ℝ) ^ 4 =
                (Real.sqrt (Fintype.card κ : ℝ) ^ 2) ^ 2 := by
                ring
            _ = (Fintype.card κ : ℝ) ^ 2 := by
                rw [hsqrt_sq]
  have hcoef :
      c ^ 4 *
          ((Fintype.card κ : ℝ) * μ4 +
            3 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * v) =
        μ4 / (Fintype.card κ : ℝ) +
          3 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) * v := by
    rw [hc4]
    field_simp [hcard_ne]
  calc
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 4 ∂Pκ =
        ∫ ωs : κ → ι, (c * S ωs) ^ 4 ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hpoint ωs]
    _ = c ^ 4 * ∫ ωs : κ → ι, S ωs ^ 4 ∂Pκ := by
          simp [mul_pow, integral_const_mul]
    _ = c ^ 4 *
          ((Fintype.card κ : ℝ) * μ4 +
            3 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * v) := by
          rw [hsum]
    _ = empiricalCentralMoment Y 4 / (Fintype.card κ : ℝ) +
        3 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) *
          empiricalCumulant2 Y ^ 2 := by
          simpa [μ4, v] using hcoef

/-- Hansen equation (10.14), fifth conditional moment of the normalized
ordinary-bootstrap sample mean, before rewriting the fifth central moment as a
sample cumulant. -/
theorem integral_fifth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 5
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalCentralMoment Y 5 /
          ((Fintype.card κ : ℝ) * Real.sqrt (Fintype.card κ : ℝ)) +
        10 * ((Fintype.card κ : ℝ) - 1) /
            ((Fintype.card κ : ℝ) * Real.sqrt (Fintype.card κ : ℝ)) *
          empiricalCumulant3 Y * empiricalCumulant2 Y := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let c : ℝ := (Real.sqrt (Fintype.card κ : ℝ))⁻¹
  let S : (κ → ι) → ℝ :=
    fun ωs => ∑ t : κ, (Y (ωs t) - empiricalMean Y)
  let μ5 : ℝ := empiricalCentralMoment Y 5
  let m32 : ℝ := empiricalCumulant3 Y * empiricalCumulant2 Y
  have hpoint : ∀ ωs : κ → ι,
      Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y) =
        c * S ωs := by
    intro ωs
    simpa [c, S] using
      normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_sum
        (κ := κ) (Y := Y) ωs
  have hsum :
      ∫ ωs : κ → ι, S ωs ^ 5 ∂Pκ =
        (Fintype.card κ : ℝ) * μ5 +
          10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * m32 := by
    simpa [S, Pκ, μ5, m32, mul_assoc] using
      integral_fifth_centered_uniformOn_fun_sum_eq
        (κ := κ) (Y := Y)
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_ne : Real.sqrt (Fintype.card κ : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hcard_pos).ne'
  have hsqrt_sq :
      Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
    Real.sq_sqrt hcard_pos.le
  have hc5 :
      c ^ 5 = ((Fintype.card κ : ℝ) ^ 2 *
        Real.sqrt (Fintype.card κ : ℝ))⁻¹ := by
    calc
      c ^ 5 = ((Real.sqrt (Fintype.card κ : ℝ))⁻¹) ^ 5 := rfl
      _ = (Real.sqrt (Fintype.card κ : ℝ) ^ 5)⁻¹ := by
          rw [inv_pow]
      _ = ((Fintype.card κ : ℝ) ^ 2 *
            Real.sqrt (Fintype.card κ : ℝ))⁻¹ := by
          congr 1
          calc
            Real.sqrt (Fintype.card κ : ℝ) ^ 5 =
                (Real.sqrt (Fintype.card κ : ℝ) ^ 2) ^ 2 *
                  Real.sqrt (Fintype.card κ : ℝ) := by
                ring
            _ = (Fintype.card κ : ℝ) ^ 2 *
                  Real.sqrt (Fintype.card κ : ℝ) := by
                rw [hsqrt_sq]
  have hcoef :
      c ^ 5 *
          ((Fintype.card κ : ℝ) * μ5 +
            10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * m32) =
        μ5 / ((Fintype.card κ : ℝ) * Real.sqrt (Fintype.card κ : ℝ)) +
          10 * ((Fintype.card κ : ℝ) - 1) /
              ((Fintype.card κ : ℝ) * Real.sqrt (Fintype.card κ : ℝ)) * m32 := by
    rw [hc5]
    field_simp [hcard_ne, hsqrt_ne]
  calc
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 5 ∂Pκ =
        ∫ ωs : κ → ι, (c * S ωs) ^ 5 ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hpoint ωs]
    _ = c ^ 5 * ∫ ωs : κ → ι, S ωs ^ 5 ∂Pκ := by
          simp [mul_pow, integral_const_mul]
    _ = c ^ 5 *
          ((Fintype.card κ : ℝ) * μ5 +
            10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * m32) := by
          rw [hsum]
    _ = empiricalCentralMoment Y 5 /
          ((Fintype.card κ : ℝ) * Real.sqrt (Fintype.card κ : ℝ)) +
        10 * ((Fintype.card κ : ℝ) - 1) /
            ((Fintype.card κ : ℝ) * Real.sqrt (Fintype.card κ : ℝ)) *
          empiricalCumulant3 Y * empiricalCumulant2 Y := by
          simpa [μ5, m32, mul_assoc] using hcoef

/-- Hansen equation (10.14), sixth conditional moment of the normalized
ordinary-bootstrap sample mean, before rewriting central moments as sample
cumulants. -/
theorem integral_sixth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 6
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalCentralMoment Y 6 / (Fintype.card κ : ℝ) ^ 2 +
        15 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) ^ 2 *
          empiricalCentralMoment Y 4 * empiricalCumulant2 Y +
        10 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) ^ 2 *
          empiricalCumulant3 Y ^ 2 +
        15 * ((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 2) /
          (Fintype.card κ : ℝ) ^ 2 * empiricalCumulant2 Y ^ 3 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let c : ℝ := (Real.sqrt (Fintype.card κ : ℝ))⁻¹
  let S : (κ → ι) → ℝ :=
    fun ωs => ∑ t : κ, (Y (ωs t) - empiricalMean Y)
  let μ2 : ℝ := empiricalCumulant2 Y
  let μ3 : ℝ := empiricalCumulant3 Y
  let μ4 : ℝ := empiricalCentralMoment Y 4
  let μ6 : ℝ := empiricalCentralMoment Y 6
  have hpoint : ∀ ωs : κ → ι,
      Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y) =
        c * S ωs := by
    intro ωs
    simpa [c, S] using
      normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_sum
        (κ := κ) (Y := Y) ωs
  have hsum :
      ∫ ωs : κ → ι, S ωs ^ 6 ∂Pκ =
        (Fintype.card κ : ℝ) * μ6 +
          15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * μ4 * μ2 +
          10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * μ3 ^ 2 +
          15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
            ((Fintype.card κ : ℝ) - 2) * μ2 ^ 3 := by
    simpa [S, Pκ, μ2, μ3, μ4, μ6, mul_assoc] using
      integral_sixth_centered_uniformOn_fun_sum_eq
        (κ := κ) (Y := Y)
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_ne : Real.sqrt (Fintype.card κ : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hcard_pos).ne'
  have hsqrt_sq :
      Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
    Real.sq_sqrt hcard_pos.le
  have hc6 : c ^ 6 = ((Fintype.card κ : ℝ) ^ 3)⁻¹ := by
    calc
      c ^ 6 = ((Real.sqrt (Fintype.card κ : ℝ))⁻¹) ^ 6 := rfl
      _ = (Real.sqrt (Fintype.card κ : ℝ) ^ 6)⁻¹ := by
          rw [inv_pow]
      _ = ((Fintype.card κ : ℝ) ^ 3)⁻¹ := by
          congr 1
          calc
            Real.sqrt (Fintype.card κ : ℝ) ^ 6 =
                (Real.sqrt (Fintype.card κ : ℝ) ^ 2) ^ 3 := by
                ring
            _ = (Fintype.card κ : ℝ) ^ 3 := by
                rw [hsqrt_sq]
  have hcoef :
      c ^ 6 *
          ((Fintype.card κ : ℝ) * μ6 +
            15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * μ4 * μ2 +
            10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * μ3 ^ 2 +
            15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
              ((Fintype.card κ : ℝ) - 2) * μ2 ^ 3) =
        μ6 / (Fintype.card κ : ℝ) ^ 2 +
          15 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) ^ 2 * μ4 * μ2 +
          10 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) ^ 2 * μ3 ^ 2 +
          15 * ((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 2) /
            (Fintype.card κ : ℝ) ^ 2 * μ2 ^ 3 := by
    rw [hc6]
    field_simp [hcard_ne]
  calc
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 6 ∂Pκ =
        ∫ ωs : κ → ι, (c * S ωs) ^ 6 ∂Pκ := by
          refine integral_congr_ae ?_
          filter_upwards with ωs
          rw [hpoint ωs]
    _ = c ^ 6 * ∫ ωs : κ → ι, S ωs ^ 6 ∂Pκ := by
          simp [mul_pow, integral_const_mul]
    _ = c ^ 6 *
          ((Fintype.card κ : ℝ) * μ6 +
            15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * μ4 * μ2 +
            10 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) * μ3 ^ 2 +
            15 * (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) - 1) *
              ((Fintype.card κ : ℝ) - 2) * μ2 ^ 3) := by
          rw [hsum]
    _ = empiricalCentralMoment Y 6 / (Fintype.card κ : ℝ) ^ 2 +
        15 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) ^ 2 *
          empiricalCentralMoment Y 4 * empiricalCumulant2 Y +
        10 * ((Fintype.card κ : ℝ) - 1) / (Fintype.card κ : ℝ) ^ 2 *
          empiricalCumulant3 Y ^ 2 +
        15 * ((Fintype.card κ : ℝ) - 1) * ((Fintype.card κ : ℝ) - 2) /
          (Fintype.card κ : ℝ) ^ 2 * empiricalCumulant2 Y ^ 3 := by
          simpa [μ2, μ3, μ4, μ6, mul_assoc] using hcoef

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Fourth central moment in terms of sample cumulants. -/
theorem empiricalCentralMoment_four_eq_cumulants (Y : ι → ℝ) :
    empiricalCentralMoment Y 4 =
      empiricalCumulant4 Y + 3 * empiricalCumulant2 Y ^ 2 := by
  simp [empiricalCumulant4]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Fifth central moment in terms of sample cumulants. -/
theorem empiricalCentralMoment_five_eq_cumulants (Y : ι → ℝ) :
    empiricalCentralMoment Y 5 =
      empiricalCumulant5 Y + 10 * empiricalCumulant3 Y * empiricalCumulant2 Y := by
  simp [empiricalCumulant5]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Sixth central moment in terms of sample cumulants. -/
theorem empiricalCentralMoment_six_eq_cumulants (Y : ι → ℝ) :
    empiricalCentralMoment Y 6 =
      empiricalCumulant6 Y + 15 * empiricalCumulant4 Y * empiricalCumulant2 Y +
        10 * empiricalCumulant3 Y ^ 2 + 15 * empiricalCumulant2 Y ^ 3 := by
  simp [empiricalCumulant6]
  ring

/-- Hansen equation (10.14), third-moment right-hand side after the
normalized bootstrap-sum cumulant scaling has been identified. -/
noncomputable def normalizedBootstrapMeanMoment3Formula
    (sampleSize : ℝ) (Y : ι → ℝ) : ℝ :=
  empiricalCumulant3 Y / Real.sqrt sampleSize

/-- Hansen equation (10.14), fourth-moment right-hand side after the
normalized bootstrap-sum cumulant scaling has been identified. -/
noncomputable def normalizedBootstrapMeanMoment4Formula
    (sampleSize : ℝ) (Y : ι → ℝ) : ℝ :=
  empiricalCumulant4 Y / sampleSize + 3 * empiricalCumulant2 Y ^ 2

/-- Hansen equation (10.14), fifth-moment right-hand side after the
normalized bootstrap-sum cumulant scaling has been identified. -/
noncomputable def normalizedBootstrapMeanMoment5Formula
    (sampleSize : ℝ) (Y : ι → ℝ) : ℝ :=
  empiricalCumulant5 Y / (sampleSize * Real.sqrt sampleSize) +
    10 * empiricalCumulant3 Y * empiricalCumulant2 Y / Real.sqrt sampleSize

/-- Hansen equation (10.14), sixth-moment right-hand side after the
normalized bootstrap-sum cumulant scaling has been identified. -/
noncomputable def normalizedBootstrapMeanMoment6Formula
    (sampleSize : ℝ) (Y : ι → ℝ) : ℝ :=
  empiricalCumulant6 Y / sampleSize ^ 2 +
    (15 * empiricalCumulant4 Y * empiricalCumulant2 Y +
      10 * empiricalCumulant3 Y ^ 2) / sampleSize +
    15 * empiricalCumulant2 Y ^ 3

/-- Hansen equation (10.14), third conditional moment in the named formula
surface. -/
theorem integral_cube_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_formula
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 3
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      normalizedBootstrapMeanMoment3Formula (Fintype.card κ : ℝ) Y := by
  simpa [normalizedBootstrapMeanMoment3Formula] using
    integral_cube_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq
      (κ := κ) (Y := Y)

/-- Hansen equation (10.14), fourth conditional moment in the named formula
surface. -/
theorem integral_fourth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_formula
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 4
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      normalizedBootstrapMeanMoment4Formula (Fintype.card κ : ℝ) Y := by
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [integral_fourth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq
    (κ := κ) (Y := Y)]
  rw [empiricalCentralMoment_four_eq_cumulants]
  simp [normalizedBootstrapMeanMoment4Formula]
  field_simp [hcard_ne]
  ring

/-- Hansen equation (10.14), fifth conditional moment in the named formula
surface. -/
theorem integral_fifth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_formula
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 5
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      normalizedBootstrapMeanMoment5Formula (Fintype.card κ : ℝ) Y := by
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_ne : Real.sqrt (Fintype.card κ : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hcard_pos).ne'
  rw [integral_fifth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq
    (κ := κ) (Y := Y)]
  rw [empiricalCentralMoment_five_eq_cumulants]
  simp [normalizedBootstrapMeanMoment5Formula]
  field_simp [hcard_ne, hsqrt_ne]
  ring

/-- Hansen equation (10.14), sixth conditional moment in the named formula
surface. -/
theorem integral_sixth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_formula
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 6
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      normalizedBootstrapMeanMoment6Formula (Fintype.card κ : ℝ) Y := by
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [integral_sixth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq
    (κ := κ) (Y := Y)]
  rw [empiricalCentralMoment_six_eq_cumulants]
  rw [empiricalCentralMoment_four_eq_cumulants]
  simp [normalizedBootstrapMeanMoment6Formula]
  field_simp [hcard_ne]
  ring

/-- Finite empirical second-moment identity for one bootstrap draw.

Under uniform resampling from a finite empirical support, the conditional
expectation of the squared norm is the finite-sample average of squared norms.
This is the norm-valued companion to Hansen's equations (10.10) and (10.12). -/
theorem integral_norm_sq_uniformOn_univ_eq_card_inv_smul_sum
    [NormedAddCommGroup E] (Y : ι → E) :
    ∫ i, ‖Y i‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ‖Y i‖ ^ 2 :=
  integral_uniformOn_univ_eq_card_inv_smul_sum (E := ℝ)
    (fun i => ‖Y i‖ ^ 2)

/-- Finite empirical fourth-moment identity for one bootstrap draw.

Under uniform resampling from a finite empirical support, the conditional
expectation of the fourth power of the norm is the finite-sample average of
fourth powers. This is the empirical moment identity used in Hansen's Theorem
10.4 Lindeberg calculation. -/
theorem integral_norm_fourth_uniformOn_univ_eq_card_inv_smul_sum
    [NormedAddCommGroup E] (Y : ι → E) :
    ∫ i, ‖Y i‖ ^ 4
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ‖Y i‖ ^ 4 :=
  integral_uniformOn_univ_eq_card_inv_smul_sum (E := ℝ)
    (fun i => ‖Y i‖ ^ 4)

/-- Finite empirical second-moment bound from a pointwise norm envelope. -/
theorem integral_norm_sq_uniformOn_univ_le_card_inv_smul_sum_sq_of_norm_le
    [NormedAddCommGroup E] (Y : ι → E) (u : ι → ℝ)
    (hY : ∀ i, ‖Y i‖ ≤ |u i|) :
    ∫ i, ‖Y i‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) ≤
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, u i ^ 2 := by
  rw [integral_norm_sq_uniformOn_univ_eq_card_inv_smul_sum]
  have hsum : ∑ i, ‖Y i‖ ^ 2 ≤ ∑ i, u i ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hsq := pow_le_pow_left₀ (norm_nonneg (Y i)) (hY i) 2
    simpa [sq_abs] using hsq
  rw [smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hsum ENNReal.toReal_nonneg

/-- Centered finite empirical squared-norm identity.

This specializes the squared-norm identity to deviations from the empirical
mean, the one-draw calculation that feeds the vector Theorem 10.2
second-moment bound. -/
theorem integral_norm_sq_centered_uniformOn_univ_eq_card_inv_smul_sum
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (Y : ι → E) :
    ∫ i, ‖Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
        ∑ i, ‖Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j‖ ^ 2 :=
  integral_norm_sq_uniformOn_univ_eq_card_inv_smul_sum
    (fun i => Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j)

/-- Centered finite empirical second-moment bound from a pointwise envelope. -/
theorem integral_norm_sq_centered_uniformOn_univ_le_card_inv_smul_sum_sq_of_norm_le
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) (u : ι → ℝ)
    (hY :
      ∀ i,
        ‖Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j‖ ≤ |u i|) :
    ∫ i, ‖Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) ≤
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, u i ^ 2 :=
  integral_norm_sq_uniformOn_univ_le_card_inv_smul_sum_sq_of_norm_le
    (fun i => Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j)
    u hY

omit [Fintype ι] in
/-- Every finite empirical statistic is square-integrable under uniform
resampling from a nonempty support. -/
theorem memLp_two_uniformOn_univ [Finite ι] [Nonempty ι]
    [NormedAddCommGroup E] (Y : ι → E) :
    MemLp Y 2 (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) := by
  exact ⟨AEStronglyMeasurable.of_discrete,
    eLpNorm_lt_top_of_finite
      (f := Y) (p := (2 : ℝ≥0∞))
      (μ := (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι))⟩

/-- Scalar empirical variance identity for one bootstrap draw.

This is the scalar version of Hansen's exact bootstrap covariance formula
(10.11): under uniform resampling from a finite empirical support, the
variance is the average squared deviation from the empirical mean. -/
theorem variance_uniformOn_univ_eq_card_inv_smul_sum_sq_centered
    (Y : ι → ℝ) :
    Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
        ∑ i, (Y i -
          ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j) ^ 2 := by
  have hmean :
      ∫ i, Y i ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j :=
    integral_uniformOn_univ_eq_card_inv_smul_sum Y
  rw [ProbabilityTheory.variance_eq_integral (measurable_of_finite Y).aemeasurable, hmean]
  exact integral_uniformOn_univ_eq_card_inv_smul_sum
    (fun i => (Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j) ^ 2)

/-- Raw second moment of a centered empirical one-draw statistic.

Since the centered empirical one-draw statistic has exact mean zero, its raw
second moment is the empirical one-draw variance. -/
theorem integral_sq_sub_empiricalMean_uniformOn_univ_eq_variance
    (Y : ι → ℝ) :
    ∫ i, (Y i - empiricalMean Y) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
  rw [variance_uniformOn_univ_eq_card_inv_smul_sum_sq_centered (Y := Y)]
  simp [integral_uniformOn_univ_eq_card_inv_smul_sum, empiricalMean]

/-- Taylor expansion at zero for the standardized centered empirical one-draw
characteristic function.

This packages Mathlib's second-order characteristic-function Taylor lemma with
the finite empirical mean-zero and variance identities. It is the local analytic
input used by the characteristic-function proof of Hansen Theorem 10.4. -/
theorem taylor_charFun_centered_standardized_uniformOn_univ
    [Nonempty ι] (Y : ι → ℝ)
    (hvar : Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) :
      Measure ι)] ≠ 0) :
    (fun t =>
      charFun
          (((ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι).map
            (fun i =>
              (Y i - empiricalMean Y) /
                Real.sqrt
                  (Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) :
                    Measure ι)])))) t -
        (1 - t ^ 2 / 2)) =o[𝓝 0] fun t => t ^ 2 := by
  let P : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let v : ℝ := Var[Y; P]
  let X : ι → ℝ := fun i => (Y i - empiricalMean Y) / Real.sqrt v
  have hvar_nonneg : 0 ≤ v := by
    dsimp [v]
    exact variance_nonneg Y P
  have hvar_pos : 0 < v := lt_of_le_of_ne hvar_nonneg (by simpa [v, P] using hvar.symm)
  have hsqrt_ne : Real.sqrt v ≠ 0 := (Real.sqrt_pos.2 hvar_pos).ne'
  have hX : AEMeasurable X P := (measurable_of_finite X).aemeasurable
  have hzero : P[X] = 0 := by
    have hcenter :
        ∫ i, Y i - empiricalMean Y ∂P = 0 := by
      simpa [P] using integral_uniformOn_univ_sub_empiricalMean_eq_zero (Y := Y)
    change ∫ i, X i ∂P = 0
    have hfun :
        X = fun i => (Real.sqrt v)⁻¹ * (Y i - empiricalMean Y) := by
      funext i
      simp [X, div_eq_mul_inv, mul_comm]
    rw [hfun, integral_const_mul, hcenter, mul_zero]
  have hone : P[X ^ 2] = 1 := by
    have hsecond :
        ∫ i, (Y i - empiricalMean Y) ^ 2 ∂P = v := by
      simpa [P, v] using integral_sq_sub_empiricalMean_uniformOn_univ_eq_variance
        (Y := Y)
    change ∫ i, X i ^ 2 ∂P = 1
    have hfun :
        (fun i => X i ^ 2) =
          fun i => (Real.sqrt v)⁻¹ ^ 2 * (Y i - empiricalMean Y) ^ 2 := by
      funext i
      simp [X, div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm]
    rw [hfun, integral_const_mul, hsecond]
    calc
      (Real.sqrt v)⁻¹ ^ 2 * v =
          (Real.sqrt v)⁻¹ ^ 2 * Real.sqrt v ^ 2 := by
            rw [Real.sq_sqrt hvar_nonneg]
      _ = 1 := by
            field_simp [hsqrt_ne]
  simpa [P, v, X] using taylor_charFun_two hX hzero hone

private theorem complex_tendsto_one_add_succ_pow_exp_of_tendsto {g : ℕ → ℂ} {t : ℂ}
    (hg : Tendsto (fun n => ((n + 1 : ℕ) : ℂ) * g n) atTop (𝓝 t)) :
    Tendsto (fun n => (1 + g n) ^ Nat.succ n) atTop (𝓝 (Complex.exp t)) := by
  let h : ℕ → ℂ := fun m => if m = 0 then 0 else g (m - 1)
  have hh : Tendsto (fun m : ℕ => (m : ℂ) * (h m)) atTop (𝓝 t) := by
    rw [← tendsto_add_atTop_iff_nat (f := fun m : ℕ => (m : ℂ) * (h m)) 1]
    refine hg.congr' ?_
    exact Eventually.of_forall fun n => by
      simp [h, Nat.cast_add]
  have hpow := Complex.tendsto_one_add_pow_exp_of_tendsto hh
  rw [← tendsto_add_atTop_iff_nat (f := fun m => (1 + h m) ^ m) 1] at hpow
  refine hpow.congr' ?_
  exact Eventually.of_forall fun n => by
    simp [h, Nat.succ_eq_add_one]

private theorem complex_tendsto_pow_succ_exp_of_isLittleO_sub_add_div {f : ℕ → ℂ} (t : ℂ)
    (hf : (fun n => f n - (1 + t / ((n + 1 : ℕ) : ℂ))) =o[atTop]
      fun n => 1 / ((n + 1 : ℕ) : ℂ)) :
    Tendsto (fun n => f n ^ Nat.succ n) atTop (𝓝 (Complex.exp t)) := by
  rw [show (fun n => f n ^ Nat.succ n) =
      (fun n => (1 + (f n - 1)) ^ Nat.succ n) by ext n; simp]
  refine complex_tendsto_one_add_succ_pow_exp_of_tendsto (t := t)
    (tendsto_sub_nhds_zero_iff.1 ?_)
  convert hf.tendsto_inv_smul_nhds_zero.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n h0
  simp
  field_simp [Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)]
  ring

private theorem complex_tendsto_pow_succ_exp_of_isLittleO_sub_add_div_tendsto
    {f a : ℕ → ℂ} {t : ℂ}
    (ha : Tendsto a atTop (𝓝 t))
    (hf : (fun n => f n - (1 + a n / ((n + 1 : ℕ) : ℂ))) =o[atTop]
      fun n => 1 / ((n + 1 : ℕ) : ℂ)) :
    Tendsto (fun n => f n ^ Nat.succ n) atTop (𝓝 (Complex.exp t)) := by
  refine complex_tendsto_pow_succ_exp_of_isLittleO_sub_add_div (f := f) t ?_
  have hscale :
      (fun n => (a n - t) / ((n + 1 : ℕ) : ℂ)) =o[atTop]
        fun n => 1 / ((n + 1 : ℕ) : ℂ) := by
    refine Asymptotics.isLittleO_of_tendsto ?_ ?_
    · intro n hn
      exfalso
      have hne : (1 / ((n + 1 : ℕ) : ℂ) : ℂ) ≠ 0 := by
        exact one_div_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
      exact hne hn
    · refine (tendsto_sub_nhds_zero_iff.2 ha).congr' ?_
      filter_upwards with n
      field_simp [Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)]
  refine (hf.add hscale).congr' ?_ EventuallyEq.rfl
  filter_upwards with n
  field_simp [Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)]
  ring

private theorem tendsto_charFun_inv_sqrt_succ_mul_pow_of_taylor
    {φ : ℝ → ℂ}
    (hφ : (fun x => φ x - (1 - x ^ 2 / 2)) =o[𝓝 0] fun x => x ^ 2)
    (t : ℝ) :
    Tendsto
      (fun n : ℕ => φ ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) ^ Nat.succ n)
      atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  apply complex_tendsto_pow_succ_exp_of_isLittleO_sub_add_div
  suffices
      (fun n : ℕ => φ ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
          (1 + (-((((Real.sqrt (n + 1 : ℝ))⁻¹ * t) ^ 2) / 2) : ℂ))) =o[atTop]
        fun n : ℕ => (((Real.sqrt (n + 1 : ℝ))⁻¹ * t) ^ 2) by
    have aux :
        (fun n : ℕ => ‖(1 / (((n + 1 : ℕ) : ℂ)) : ℂ)‖) =
          fun n : ℕ => ‖(1 / (((n + 1 : ℕ) : ℝ)) : ℝ)‖ := by
      funext n
      simp only [one_div, norm_inv]
      congr 1
      calc
        ‖(((n + 1 : ℕ) : ℂ))‖ = (((n + 1 : ℕ) : ℝ)) := by
          simpa using Complex.norm_natCast (n + 1)
        _ = |(((n + 1 : ℕ) : ℝ))| :=
          (abs_of_nonneg (Nat.cast_nonneg (n + 1))).symm
    rw [← Asymptotics.isLittleO_norm_right, aux, Asymptotics.isLittleO_norm_right]
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert this using 4 with n
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 :=
        (Real.sqrt_pos.2 (by positivity : 0 < (n : ℝ) + 1)).ne'
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]
    · rename_i m
      norm_cast
      simp only [Nat.cast_add, Nat.cast_one, one_div]
      have hsqrt_ne : Real.sqrt ((m : ℝ) + 1) ≠ 0 :=
        (Real.sqrt_pos.2 (by positivity : 0 < (m : ℝ) + 1)).ne'
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ) + 1)]
  have hscale :
      Tendsto (fun n : ℕ => (Real.sqrt (n + 1 : ℝ))⁻¹ * t) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
      refine ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat 1)).congr' ?_
      exact Eventually.of_forall fun n => by simp [Nat.cast_add]
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <|
      Real.tendsto_sqrt_atTop.comp hnat)
  convert hφ.comp_tendsto hscale using 2
  simp
  ring

/-- Gaussian characteristic-function power limit for a standardized centered
empirical one-draw law with fixed support.

This is the fixed-support analytic bridge behind the characteristic-function
proof of Hansen Theorem 10.4: once the empirical one-draw statistic is centered
and divided by its empirical standard deviation, the `n+1` iid bootstrap draws
have the standard-normal characteristic-function limit. -/
theorem charFun_centered_standardized_uniformOn_univ_inv_sqrt_succ_pow_tendsto
    [Nonempty ι] (Y : ι → ℝ)
    (hvar : Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) :
      Measure ι)] ≠ 0) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (charFun
            (((ProbabilityTheory.uniformOn (Set.univ : Set ι) :
              Measure ι).map
              (fun i =>
                (Y i - empiricalMean Y) /
                  Real.sqrt
                    (Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) :
                      Measure ι)]))))
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t)) ^ Nat.succ n)
      atTop
      (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) :=
  tendsto_charFun_inv_sqrt_succ_mul_pow_of_taylor
    (taylor_charFun_centered_standardized_uniformOn_univ (Y := Y) hvar) t

/-- Gaussian characteristic-function power limit for a centered empirical
one-draw law with fixed support.

This removes the standardization from
`charFun_centered_standardized_uniformOn_univ_inv_sqrt_succ_pow_tendsto`: the
fixed-support limit has the empirical one-draw variance as its Gaussian scale. -/
theorem charFun_centered_uniformOn_univ_inv_sqrt_succ_pow_tendsto
    [Nonempty ι] (Y : ι → ℝ)
    (hvar : Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) :
      Measure ι)] ≠ 0) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (charFun
            (((ProbabilityTheory.uniformOn (Set.univ : Set ι) :
              Measure ι).map
              (fun i => Y i - empiricalMean Y)))
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t)) ^ Nat.succ n)
      atTop
      (𝓝 (Complex.exp
        (-(((Real.sqrt
          (Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) :
            Measure ι)]) * t : ℝ) : ℂ) ^ 2) / 2))) := by
  let P : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let v : ℝ := Var[Y; P]
  let Z : ι → ℝ := fun i => Y i - empiricalMean Y
  let σ : ℝ := Real.sqrt v
  have hv_nonneg : 0 ≤ v := by
    dsimp [v]
    exact variance_nonneg Y P
  have hσ_ne : σ ≠ 0 := by
    exact (Real.sqrt_pos.2 (lt_of_le_of_ne hv_nonneg (by simpa [v, P] using hvar.symm))).ne'
  have hstd :=
    charFun_centered_standardized_uniformOn_univ_inv_sqrt_succ_pow_tendsto
      (Y := Y) hvar (σ * t)
  refine hstd.congr' ?_
  exact Eventually.of_forall fun n => by
    change
      (charFun (P.map (fun i => Z i / σ))
          ((Real.sqrt (n + 1 : ℝ))⁻¹ * (σ * t))) ^ Nat.succ n =
        (charFun (P.map Z) ((Real.sqrt (n + 1 : ℝ))⁻¹ * t)) ^ Nat.succ n
    have hscale :
        charFun (P.map (fun i => Z i / σ))
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * (σ * t)) =
          charFun (P.map Z)
            (σ⁻¹ * ((Real.sqrt (n + 1 : ℝ))⁻¹ * (σ * t))) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (charFun_map_mul_comp
          (μ := P)
          (f := Z)
          ((measurable_of_finite Z).aemeasurable)
          σ⁻¹ ((Real.sqrt (n + 1 : ℝ))⁻¹ * (σ * t)))
    calc
      (charFun (P.map (fun i => Z i / σ))
          ((Real.sqrt (n + 1 : ℝ))⁻¹ * (σ * t))) ^ Nat.succ n =
          (charFun (P.map Z)
            (σ⁻¹ * ((Real.sqrt (n + 1 : ℝ))⁻¹ * (σ * t)))) ^ Nat.succ n := by
            rw [hscale]
      _ = (charFun (P.map Z) ((Real.sqrt (n + 1 : ℝ))⁻¹ * t)) ^ Nat.succ n := by
            congr 2
            field_simp [hσ_ne]

/-- Empirical one-draw variance over the first `n+1` scalar observations. -/
noncomputable def empiricalVarianceFinSucc (Y : ℕ → ℝ) (n : ℕ) : ℝ :=
  Var[fun i : Fin (n + 1) => Y i.val;
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
      Measure (Fin (n + 1)))]

/-- Centered empirical one-draw characteristic function over the first `n+1`
scalar observations. -/
noncomputable def centeredEmpiricalCharFunFinSucc
    (Y : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  charFun
    ((ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
      Measure (Fin (n + 1))).map
      (fun i : Fin (n + 1) =>
        Y i.val - empiricalMean (fun j : Fin (n + 1) => Y j.val)))
    u

/-- Centered finite empirical square-tail integral.

This is the scalar Lindeberg tail for the centered one-draw empirical
bootstrap summand, evaluated at a deterministic scale `u`. -/
noncomputable def centeredEmpiricalTailSqFinSucc
    (Y : ℕ → ℝ) (n : ℕ) (u δ : ℝ) : ℝ :=
  ∫ i : Fin (n + 1),
    Set.indicator
      {i : Fin (n + 1) |
        δ ≤ |u * (Y i.val -
          empiricalMean (fun j : Fin (n + 1) => Y j.val))|}
      (fun i =>
        (Y i.val - empiricalMean (fun j : Fin (n + 1) => Y j.val)) ^ 2) i
    ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
      Measure (Fin (n + 1)))

/-- Uncentered finite empirical square-tail integral.

This records the fixed-threshold square tails used to dominate the centered
moving `sqrt n` tails in the diagonal characteristic-function argument. -/
noncomputable def empiricalTailSqFinSucc
    (Y : ℕ → ℝ) (n : ℕ) (R : ℝ) : ℝ :=
  ∫ i : Fin (n + 1),
    Set.indicator {i : Fin (n + 1) | R ≤ |Y i.val|}
      (fun i => (Y i.val) ^ 2) i
    ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
      Measure (Fin (n + 1)))

/-- Centered empirical square tails are dominated by fixed uncentered square
tails once the empirical mean is bounded and the moving scaled-tail event
implies the fixed raw-tail event. -/
theorem centeredEmpiricalTailSqFinSucc_le_const_mul_empiricalTailSqFinSucc
    (Y : ℕ → ℝ) (n : ℕ) {u δ M R : ℝ}
    (hM :
      |empiricalMean (fun i : Fin (n + 1) => Y i.val)| ≤ M)
    (hR : 1 ≤ R)
    (himp : ∀ i : Fin (n + 1),
      δ ≤ |u * (Y i.val -
        empiricalMean (fun j : Fin (n + 1) => Y j.val))| →
      R ≤ |Y i.val|) :
    centeredEmpiricalTailSqFinSucc Y n u δ ≤
      (2 + 2 * M ^ 2) * empiricalTailSqFinSucc Y n R := by
  classical
  let P : Measure (Fin (n + 1)) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
  let m : ℝ := empiricalMean (fun i : Fin (n + 1) => Y i.val)
  let scaledTail : Set (Fin (n + 1)) :=
    {i : Fin (n + 1) | δ ≤ |u * (Y i.val - m)|}
  let rawTail : Set (Fin (n + 1)) :=
    {i : Fin (n + 1) | R ≤ |Y i.val|}
  have hM_nonneg : 0 ≤ M :=
    (abs_nonneg m).trans hM
  have hcoeff_nonneg : 0 ≤ 2 + 2 * M ^ 2 := by positivity
  have hleft_int :
      Integrable
        (fun i : Fin (n + 1) =>
          Set.indicator scaledTail (fun i => (Y i.val - m) ^ 2) i)
        P :=
    Integrable.of_finite
  have hright_int :
      Integrable
        (fun i : Fin (n + 1) =>
          (2 + 2 * M ^ 2) *
            Set.indicator rawTail (fun i => (Y i.val) ^ 2) i)
        P :=
    Integrable.of_finite
  change
    ∫ i : Fin (n + 1),
        Set.indicator scaledTail (fun i => (Y i.val - m) ^ 2) i ∂P ≤
      (2 + 2 * M ^ 2) *
        ∫ i : Fin (n + 1),
          Set.indicator rawTail (fun i => (Y i.val) ^ 2) i ∂P
  rw [← integral_const_mul]
  refine integral_mono hleft_int hright_int ?_
  intro i
  by_cases hscaled : i ∈ scaledTail
  · have hraw : i ∈ rawTail := by
      exact himp i hscaled
    rw [Set.indicator_of_mem hscaled]
    change (Y i.val - m) ^ 2 ≤
      (2 + 2 * M ^ 2) *
        Set.indicator rawTail (fun i => (Y i.val) ^ 2) i
    rw [Set.indicator_of_mem hraw]
    have hy_abs_one : 1 ≤ |Y i.val| := hR.trans hraw
    have hy_sq_one : 1 ≤ (Y i.val) ^ 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hy_abs_one (abs_nonneg (Y i.val))
      exact hy_abs_one.trans (by simpa [sq_abs, pow_two] using hmul)
    have hm_sq_le : m ^ 2 ≤ M ^ 2 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg m) hM 2
      simpa [sq_abs] using hpow
    have hbasic : (Y i.val - m) ^ 2 ≤ 2 * (Y i.val) ^ 2 + 2 * m ^ 2 := by
      nlinarith [sq_nonneg (Y i.val + m)]
    have hM_sq_mul : M ^ 2 ≤ M ^ 2 * (Y i.val) ^ 2 := by
      calc
        M ^ 2 = M ^ 2 * 1 := by ring
        _ ≤ M ^ 2 * (Y i.val) ^ 2 :=
          mul_le_mul_of_nonneg_left hy_sq_one (sq_nonneg M)
    nlinarith
  · rw [Set.indicator_of_notMem hscaled]
    exact mul_nonneg hcoeff_nonneg
      (Set.indicator_nonneg (fun i _ => sq_nonneg (Y i.val)) i)

/-- Centered empirical square tails vanish when empirical means are bounded
and fixed uncentered empirical square tails can be made uniformly small.

This deterministic constructor is the pathwise truncation bridge needed to
turn strong-law fixed-tail controls into the centered moving Lindeberg tail used
by the Taylor remainder. -/
theorem centeredEmpiricalTailSqFinSucc_tendsto_zero_of_empiricalMean_tendsto_tail
    (Y : ℕ → ℝ) {m : ℝ}
    (hmean :
      Tendsto
        (fun n : ℕ =>
          empiricalMean (fun i : Fin (n + 1) => Y i.val))
        atTop (𝓝 m))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ᶠ n in atTop, empiricalTailSqFinSucc Y n R ≤ ε)
    (u : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun n : ℕ =>
        centeredEmpiricalTailSqFinSucc Y n
          ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ)
      atTop (𝓝 0) := by
  classical
  let M : ℝ := |m| + 1
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hmean_bound :
      ∀ᶠ n in atTop,
        |empiricalMean (fun i : Fin (n + 1) => Y i.val)| ≤ M := by
    have hball : Metric.ball m (1 : ℝ) ∈ 𝓝 m :=
      Metric.ball_mem_nhds _ zero_lt_one
    filter_upwards [hmean.eventually hball] with n hn
    have habs : |empiricalMean (fun i : Fin (n + 1) => Y i.val) - m| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    have htri :
        |empiricalMean (fun i : Fin (n + 1) => Y i.val)| ≤
          |empiricalMean (fun i : Fin (n + 1) => Y i.val) - m| + |m| := by
      calc
        |empiricalMean (fun i : Fin (n + 1) => Y i.val)| =
            |(empiricalMean (fun i : Fin (n + 1) => Y i.val) - m) + m| := by
              rw [sub_add_cancel]
        _ ≤ |empiricalMean (fun i : Fin (n + 1) => Y i.val) - m| + |m| :=
            abs_add_le _ _
    dsimp [M]
    linarith
  have hscale :
      Tendsto (fun n : ℕ => (Real.sqrt (n + 1 : ℝ))⁻¹ * u) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
      refine ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat 1)).congr' ?_
      exact Eventually.of_forall fun n => by simp [Nat.cast_add]
    rw [← zero_mul u]
    exact .mul_const u (tendsto_inv_atTop_zero.comp <|
      Real.tendsto_sqrt_atTop.comp hnat)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards with n
    have hnonneg :
        0 ≤
          centeredEmpiricalTailSqFinSucc Y n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ := by
      dsimp [centeredEmpiricalTailSqFinSucc]
      exact integral_nonneg fun i =>
        Set.indicator_nonneg
          (fun i _ =>
            sq_nonneg
              (Y i.val - empiricalMean (fun j : Fin (n + 1) => Y j.val))) i
    linarith
  · intro a ha
    let C : ℝ := 2 + 2 * M ^ 2
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hCden_pos : 0 < C + 1 := by positivity
    let εtail : ℝ := a / (C + 1)
    have hεtail_pos : 0 < εtail := by
      dsimp [εtail]
      positivity
    rcases htail εtail hεtail_pos with ⟨R, hR, htail_event⟩
    have hR_nonneg : 0 ≤ R := by linarith
    have hRM_nonneg : 0 ≤ R + M := add_nonneg hR_nonneg hM_nonneg
    have hscale_event :
        ∀ᶠ (n : ℕ) in atTop,
          |(Real.sqrt (n + 1 : ℝ))⁻¹ * u| * (R + M) < δ := by
      have hscale_abs :
          Tendsto
            (fun n : ℕ => |(Real.sqrt (n + 1 : ℝ))⁻¹ * u|)
            atTop (𝓝 0) := by
        simpa only [Function.comp_apply, abs_zero] using
          (continuous_abs.tendsto 0).comp hscale
      have hprod :
          Tendsto
            (fun n : ℕ =>
              |(Real.sqrt (n + 1 : ℝ))⁻¹ * u| * (R + M))
            atTop (𝓝 0) := by
        simpa using hscale_abs.mul_const (R + M)
      exact hprod.eventually (Iio_mem_nhds hδ)
    have hC_eps_lt : C * εtail < a := by
      have hfrac : C / (C + 1) < 1 := by
        rw [div_lt_one hCden_pos]
        linarith
      have heq : C * εtail = a * (C / (C + 1)) := by
        dsimp [εtail]
        field_simp [hCden_pos.ne']
      rw [heq]
      calc
        a * (C / (C + 1)) < a * 1 :=
          mul_lt_mul_of_pos_left hfrac ha
        _ = a := by ring
    filter_upwards [hmean_bound, htail_event, hscale_event] with n hmean_n htail_n hscale_n
    have hle :=
      centeredEmpiricalTailSqFinSucc_le_const_mul_empiricalTailSqFinSucc
        (Y := Y) (n := n) (u := (Real.sqrt (n + 1 : ℝ))⁻¹ * u)
        (δ := δ) (M := M) (R := R) hmean_n hR ?_
    · have hmul_le : C * empiricalTailSqFinSucc Y n R ≤ C * εtail :=
        mul_le_mul_of_nonneg_left htail_n hC_nonneg
      exact lt_of_le_of_lt (hle.trans hmul_le) hC_eps_lt
    · intro i hi
      by_contra hnot
      have hy_lt : |Y i.val| < R := not_le.mp hnot
      let mean_n : ℝ := empiricalMean (fun j : Fin (n + 1) => Y j.val)
      have hdiff_abs :
          |Y i.val - mean_n| ≤ |Y i.val| + |mean_n| := by
        simpa [sub_eq_add_neg] using abs_add_le (Y i.val) (-mean_n)
      have hdiff_lt : |Y i.val - mean_n| < R + M := by
        dsimp [mean_n]
        linarith
      have hscale_abs_nonneg : 0 ≤ |(Real.sqrt (n + 1 : ℝ))⁻¹ * u| :=
        abs_nonneg _
      have hprod_le :
          |(Real.sqrt (n + 1 : ℝ))⁻¹ * u| * |Y i.val - mean_n| ≤
            |(Real.sqrt (n + 1 : ℝ))⁻¹ * u| * (R + M) :=
        mul_le_mul_of_nonneg_left hdiff_lt.le hscale_abs_nonneg
      have hscaled_lt :
          |((Real.sqrt (n + 1 : ℝ))⁻¹ * u) *
              (Y i.val - mean_n)| < δ := by
        calc
          |((Real.sqrt (n + 1 : ℝ))⁻¹ * u) * (Y i.val - mean_n)| =
              |(Real.sqrt (n + 1 : ℝ))⁻¹ * u| * |Y i.val - mean_n| := by
                rw [abs_mul]
          _ ≤ |(Real.sqrt (n + 1 : ℝ))⁻¹ * u| * (R + M) := hprod_le
          _ < δ := hscale_n
      exact not_le_of_gt hscaled_lt hi

/-- Scalar Gaussian characteristic-function exponent `-t² σ² / 2`. -/
noncomputable def scalarGaussianCharFunExponent (t variance : ℝ) : ℂ :=
  -((t : ℂ) ^ 2 * (variance : ℂ) / 2)

/-- The complex reciprocal of `n+1`, written without nested casts in theorem
statements. -/
noncomputable def complexInvNatSucc (n : ℕ) : ℂ :=
  (Nat.succ n : ℂ)⁻¹

private theorem complex_exp_I_sub_quadratic_isLittleO :
    (fun x : ℝ =>
      Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)) =o[𝓝 0]
      fun x : ℝ => x ^ 2 := by
  let δ₁ : Measure ℝ := Measure.dirac (1 : ℝ)
  have hmem : MemLp id 2 δ₁ := by
    exact MemLp.ae_eq (ae_eq_dirac (fun x : ℝ => x)).symm
      (memLp_const (1 : ℝ))
  have ht :
      (fun x : ℝ => charFun δ₁ x - taylorWithinEval (charFun δ₁) 2 Set.univ 0 x) =o[𝓝 0]
        fun x : ℝ => (x - 0) ^ 2 :=
    taylor_isLittleO_univ
      (f := charFun δ₁) (x₀ := 0) (n := 2) (contDiff_charFun hmem)
  refine ht.congr' ?_ ?_
  · filter_upwards with x
    rw [taylorWithinEval_charFun_zero hmem]
    rw [charFun_apply_real]
    norm_num [δ₁, Finset.sum_range_succ]
    have hsq : ((x : ℂ) * Complex.I) ^ 2 = -((x : ℂ) ^ 2) := by
      rw [mul_pow, Complex.I_sq]
      ring
    rw [hsq]
    ring
  · filter_upwards with x
    ring

private theorem complex_exp_I_sub_quadratic_norm_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤
      2 + |x| + x ^ 2 / 2 := by
  let e : ℂ := Complex.exp ((x : ℂ) * Complex.I)
  let a : ℂ := (x : ℂ) * Complex.I
  let b : ℂ := (x : ℂ) ^ 2 / 2
  have he : ‖e‖ = 1 := by
    simp [e]
  have ha : ‖a‖ = |x| := by
    simp [a, Real.norm_eq_abs]
  have hb : ‖b‖ = x ^ 2 / 2 := by
    simp [b, Real.norm_eq_abs, sq_abs]
  have hpoly : ‖1 + a - b‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ + ‖b‖ := by
    calc
      ‖1 + a - b‖ ≤ ‖1 + a‖ + ‖b‖ := by
        simpa [sub_eq_add_neg] using norm_add_le (1 + a) (-b)
      _ ≤ (‖(1 : ℂ)‖ + ‖a‖) + ‖b‖ := by
        linarith [norm_add_le (1 : ℂ) a]
      _ = ‖(1 : ℂ)‖ + ‖a‖ + ‖b‖ := by ring
  calc
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ =
        ‖e - (1 + a - b)‖ := rfl
    _ ≤ ‖e‖ + ‖1 + a - b‖ := norm_sub_le e (1 + a - b)
    _ ≤ ‖e‖ + (‖(1 : ℂ)‖ + ‖a‖ + ‖b‖) := by
      linarith
    _ = 2 + |x| + x ^ 2 / 2 := by
      rw [he, ha, hb]
      norm_num
      ring

private theorem complex_exp_I_sub_quadratic_norm_le_const_mul_sq_of_le_abs
    {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ |x|) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤
      (2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2) * x ^ 2 := by
  have hbase := complex_exp_I_sub_quadratic_norm_le x
  have hδ_ne : δ ≠ 0 := hδ.ne'
  have hδ2_le_x2 : δ ^ 2 ≤ x ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ hδ.le hx 2
  have htwo_le : 2 ≤ (2 * δ⁻¹ ^ 2) * x ^ 2 := by
    have hscale_nonneg : 0 ≤ 2 * δ⁻¹ ^ 2 := by positivity
    have hmul :
        (2 * δ⁻¹ ^ 2) * δ ^ 2 ≤ (2 * δ⁻¹ ^ 2) * x ^ 2 :=
      mul_le_mul_of_nonneg_left hδ2_le_x2 hscale_nonneg
    have hleft : (2 * δ⁻¹ ^ 2) * δ ^ 2 = 2 := by
      field_simp [hδ_ne]
    calc
      2 = (2 * δ⁻¹ ^ 2) * δ ^ 2 := hleft.symm
      _ ≤ (2 * δ⁻¹ ^ 2) * x ^ 2 := hmul
  have habs_le : |x| ≤ δ⁻¹ * x ^ 2 := by
    have hmul :
        δ * |x| ≤ |x| * |x| :=
      mul_le_mul_of_nonneg_right hx (abs_nonneg x)
    have hmul' : δ * |x| ≤ x ^ 2 := by
      simpa [sq_abs, pow_two] using hmul
    have hscale :
        δ⁻¹ * (δ * |x|) ≤ δ⁻¹ * x ^ 2 :=
      mul_le_mul_of_nonneg_left hmul' (inv_nonneg.mpr hδ.le)
    have hleft : δ⁻¹ * (δ * |x|) = |x| := by
      field_simp [hδ_ne]
    calc
      |x| = δ⁻¹ * (δ * |x|) := hleft.symm
      _ ≤ δ⁻¹ * x ^ 2 := hscale
  calc
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤
        2 + |x| + x ^ 2 / 2 := hbase
    _ ≤ (2 * δ⁻¹ ^ 2) * x ^ 2 + δ⁻¹ * x ^ 2 + (1 / 2) * x ^ 2 := by
      nlinarith [htwo_le, habs_le]
    _ = (2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2) * x ^ 2 := by ring

private theorem complex_exp_I_sub_quadratic_norm_le_eta_mul_sq_near_zero
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤
        η * x ^ 2 := by
  have hnear := complex_exp_I_sub_quadratic_isLittleO.def hη
  rcases Metric.mem_nhds_iff.1 hnear with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hxball : x ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Real.dist_eq, abs_sub_comm] using hx
  have hle := hδsub hxball
  simpa [Real.norm_eq_abs, sq_abs] using hle

private theorem complex_exp_I_sub_quadratic_norm_le_split
    {δ η x : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η)
    (hsmall : ∀ y : ℝ, |y| < δ →
      ‖Complex.exp ((y : ℂ) * Complex.I) -
          (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤
        η * y ^ 2) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤
      η * x ^ 2 +
        (2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2) *
          Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) x := by
  by_cases hxsmall : |x| < δ
  · have hnot : x ∉ {y : ℝ | δ ≤ |y|} := by
      exact not_le.mpr hxsmall
    rw [Set.indicator_of_notMem hnot]
    have hsq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    have htail_nonneg :
        0 ≤ (2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2) * 0 := by norm_num
    nlinarith [hsmall x hxsmall]
  · have htail : δ ≤ |x| := le_of_not_gt hxsmall
    have hmem : x ∈ {y : ℝ | δ ≤ |y|} := htail
    rw [Set.indicator_of_mem hmem]
    have hglobal :=
      complex_exp_I_sub_quadratic_norm_le_const_mul_sq_of_le_abs hδ htail
    have hsq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    have hηterm_nonneg : 0 ≤ η * x ^ 2 := mul_nonneg hη hsq_nonneg
    nlinarith [hglobal, hηterm_nonneg]

/-- Finite empirical characteristic-function Taylor remainder bound.

For the ordinary `Fin (n+1)` empirical one-draw law, the diagonal
characteristic-function remainder is bounded by the empirical integral of the
pointwise second-order exponential remainder.  The right side is split into a
small quadratic term and a large-tail quadratic term, matching the Lindeberg
calculation used in Hansen Theorem 10.4. -/
private theorem centeredEmpiricalCharFunFinSucc_remainder_norm_le_integral_split
    (Y : ℕ → ℝ) (n : ℕ) (t δ η : ℝ)
    (hδ : 0 < δ) (hη : 0 ≤ η)
    (hsmall : ∀ y : ℝ, |y| < δ →
      ‖Complex.exp ((y : ℂ) * Complex.I) -
          (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤
        η * y ^ 2) :
    ‖centeredEmpiricalCharFunFinSucc Y n ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
        (1 +
          scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
            complexInvNatSucc n)‖ ≤
      ∫ i : Fin (n + 1),
        η *
            (((Real.sqrt (n + 1 : ℝ))⁻¹ * t) *
              (Y i.val - empiricalMean (fun j : Fin (n + 1) => Y j.val))) ^ 2 +
          (2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2) *
            Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2)
              (((Real.sqrt (n + 1 : ℝ))⁻¹ * t) *
                (Y i.val - empiricalMean (fun j : Fin (n + 1) => Y j.val)))
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1))) := by
  classical
  let P : Measure (Fin (n + 1)) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
  let Z : Fin (n + 1) → ℝ :=
    fun i => Y i.val - empiricalMean (fun j : Fin (n + 1) => Y j.val)
  let u : ℝ := (Real.sqrt (n + 1 : ℝ))⁻¹ * t
  let C : ℝ := 2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2
  change
    ‖centeredEmpiricalCharFunFinSucc Y n u -
        (1 +
          scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
            complexInvNatSucc n)‖ ≤
      ∫ i : Fin (n + 1),
        η * (u * Z i) ^ 2 +
          C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i)
        ∂P
  have hcenter : ∫ i, Z i ∂P = 0 := by
    simpa [P, Z] using
      integral_uniformOn_univ_sub_empiricalMean_eq_zero
        (Y := fun j : Fin (n + 1) => Y j.val)
  have hsecond :
      ∫ i, (Z i) ^ 2 ∂P = empiricalVarianceFinSucc Y n := by
    simpa [P, Z, empiricalVarianceFinSucc] using
      integral_sq_sub_empiricalMean_uniformOn_univ_eq_variance
        (Y := fun j : Fin (n + 1) => Y j.val)
  have hNpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsqrt_ne : Real.sqrt ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hNpos).ne'
  have hu2_real :
      u ^ 2 = t ^ 2 * (((n + 1 : ℕ) : ℝ))⁻¹ := by
    have hsqrt_sq :
        Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    dsimp [u]
    norm_num [Nat.cast_add]
    rw [mul_pow]
    rw [show (Real.sqrt ((n : ℝ) + 1))⁻¹ ^ 2 = ((n : ℝ) + 1)⁻¹ by
      have hNne : (n : ℝ) + 1 ≠ 0 := by positivity
      have hsqrt_ne' : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
        exact (Real.sqrt_pos.2 (by positivity)).ne'
      field_simp [hsqrt_ne', hNne]
      rw [hsqrt_sq]]
    ring
  have hu2_complex :
      (u : ℂ) ^ 2 = (t : ℂ) ^ 2 * complexInvNatSucc n := by
    calc
      (u : ℂ) ^ 2 = ((u ^ 2 : ℝ) : ℂ) := by norm_num
      _ = ((t ^ 2 * (((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
        rw [hu2_real]
      _ = (t : ℂ) ^ 2 * complexInvNatSucc n := by
        simp [complexInvNatSucc, Nat.succ_eq_add_one]
  let expTerm : Fin (n + 1) → ℂ :=
    fun i => Complex.exp (((u * Z i : ℝ) : ℂ) * Complex.I)
  let constTerm : Fin (n + 1) → ℂ := fun _ => 1
  let linTerm : Fin (n + 1) → ℂ :=
    fun i => ((u * Z i : ℝ) : ℂ) * Complex.I
  let sqTerm : Fin (n + 1) → ℂ :=
    fun i => ((u * Z i : ℝ) : ℂ) ^ 2 / 2
  let quadTerm : Fin (n + 1) → ℂ :=
    fun i => constTerm i + linTerm i - sqTerm i
  let remTerm : Fin (n + 1) → ℂ := fun i => expTerm i - quadTerm i
  have hphi :
      centeredEmpiricalCharFunFinSucc Y n u = ∫ i, expTerm i ∂P := by
    change charFun (P.map Z) u = ∫ i, expTerm i ∂P
    rw [charFun_apply_real,
      integral_map (by exact (measurable_of_finite Z).aemeasurable) (by fun_prop)]
    simp [expTerm, mul_assoc]
  have hconst_int : Integrable constTerm P :=
    integrable_const _
  have hlin_int : Integrable linTerm P :=
    Integrable.of_finite
  have hquad_int : Integrable sqTerm P :=
    Integrable.of_finite
  have hlinear :
      ∫ i, linTerm i ∂P = 0 := by
    change ∫ i, ((u * Z i : ℝ) : ℂ) * Complex.I ∂P = 0
    calc
      ∫ i, ((u * Z i : ℝ) : ℂ) * Complex.I ∂P =
          (∫ i, ((u * Z i : ℝ) : ℂ) ∂P) * Complex.I := by
            exact integral_mul_const (μ := P) Complex.I
              (fun i : Fin (n + 1) => ((u * Z i : ℝ) : ℂ))
      _ = ((∫ i, u * Z i ∂P : ℝ) : ℂ) * Complex.I := by
            rw [integral_complex_ofReal]
      _ = ((u * ∫ i, Z i ∂P : ℝ) : ℂ) * Complex.I := by
            rw [integral_const_mul]
      _ = 0 := by
            rw [hcenter]
            simp
  have hquad_real :
      ∫ i, (u * Z i) ^ 2 / 2 ∂P =
        u ^ 2 * empiricalVarianceFinSucc Y n / 2 := by
    have hfun :
        (fun i : Fin (n + 1) => (u * Z i) ^ 2 / 2) =
          fun i : Fin (n + 1) => (u ^ 2 / 2) * (Z i) ^ 2 := by
      funext i
      ring
    rw [hfun, integral_const_mul, hsecond]
    ring
  have hquad :
      ∫ i, sqTerm i ∂P =
        (u : ℂ) ^ 2 * (empiricalVarianceFinSucc Y n : ℂ) / 2 := by
    change
      ∫ i, ((u * Z i : ℝ) : ℂ) ^ 2 / 2 ∂P =
        (u : ℂ) ^ 2 * (empiricalVarianceFinSucc Y n : ℂ) / 2
    have hfun :
        (fun i : Fin (n + 1) => ((u * Z i : ℝ) : ℂ) ^ 2 / 2) =
          fun i : Fin (n + 1) => (((u * Z i) ^ 2 / 2 : ℝ) : ℂ) := by
      funext i
      norm_num
    rw [hfun, integral_complex_ofReal, hquad_real]
    norm_num
  have hpoly_int :
      ∫ i, quadTerm i ∂P =
        1 +
          scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
            complexInvNatSucc n := by
    have hconst : ∫ i, constTerm i ∂P = 1 := by
      simp [P, constTerm]
    calc
      ∫ i, quadTerm i ∂P =
          ∫ i, (constTerm i + linTerm i) - sqTerm i ∂P := rfl
      _ =
          ∫ i, constTerm i + linTerm i ∂P -
            ∫ i, sqTerm i ∂P :=
            integral_sub (hconst_int.add hlin_int) hquad_int
      _ =
          (∫ i, constTerm i ∂P) + ∫ i, linTerm i ∂P -
            ∫ i, sqTerm i ∂P := by
            rw [integral_add hconst_int hlin_int]
      _ = 1 - ((u : ℂ) ^ 2 * (empiricalVarianceFinSucc Y n : ℂ) / 2) := by
            rw [hconst, hlinear, hquad]
            ring
      _ = 1 +
          scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
            complexInvNatSucc n := by
            rw [hu2_complex]
            simp [scalarGaussianCharFunExponent]
            ring
  have hexp_int : Integrable expTerm P := Integrable.of_finite
  have hquadTerm_int : Integrable quadTerm P :=
    (hconst_int.add hlin_int).sub hquad_int
  have hrem_eq :
      centeredEmpiricalCharFunFinSucc Y n u -
          (1 +
            scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
              complexInvNatSucc n) =
        ∫ i, remTerm i ∂P := by
    calc
      centeredEmpiricalCharFunFinSucc Y n u -
          (1 +
            scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
              complexInvNatSucc n) =
          ∫ i, expTerm i ∂P - ∫ i, quadTerm i ∂P := by
            rw [hphi, hpoly_int]
      _ = ∫ i, expTerm i - quadTerm i ∂P := by
            rw [integral_sub hexp_int hquadTerm_int]
      _ = ∫ i, remTerm i ∂P := rfl
  have hbound_int :
      Integrable
        (fun i : Fin (n + 1) =>
          η * (u * Z i) ^ 2 +
            C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i))
        P :=
    Integrable.of_finite
  have hpoint :
      ∀ i : Fin (n + 1),
        ‖remTerm i‖ ≤
          η * (u * Z i) ^ 2 +
            C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i) := by
    intro i
    simpa [remTerm, expTerm, quadTerm, constTerm, linTerm, sqTerm, C,
      Complex.ofReal_mul] using
      complex_exp_I_sub_quadratic_norm_le_split
        (x := u * Z i) hδ hη hsmall
  calc
    ‖centeredEmpiricalCharFunFinSucc Y n u -
        (1 +
          scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
            complexInvNatSucc n)‖ =
        ‖∫ i, remTerm i ∂P‖ := by rw [hrem_eq]
    _ ≤
        ∫ i : Fin (n + 1),
          η * (u * Z i) ^ 2 +
            C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i)
          ∂P :=
        norm_integral_le_of_norm_le hbound_int (ae_of_all P hpoint)

/-- Scaled finite empirical characteristic-function Taylor remainder bound.

After multiplying by `n+1`, the small part of the empirical Taylor bound is
`η t²` times the empirical variance and the large part is `t²` times the
centered Lindeberg tail. -/
theorem centeredEmpiricalCharFunFinSucc_remainder_scaled_norm_le
    (Y : ℕ → ℝ) (n : ℕ) (t δ η : ℝ)
    (hδ : 0 < δ) (hη : 0 ≤ η)
    (hsmall : ∀ y : ℝ, |y| < δ →
      ‖Complex.exp ((y : ℂ) * Complex.I) -
          (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤
        η * y ^ 2) :
    ((n + 1 : ℕ) : ℝ) *
        ‖centeredEmpiricalCharFunFinSucc Y n ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
          (1 +
            scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
              complexInvNatSucc n)‖ ≤
      η * t ^ 2 * empiricalVarianceFinSucc Y n +
        (2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2) * t ^ 2 *
          ∫ i : Fin (n + 1),
            Set.indicator
              {i : Fin (n + 1) |
                δ ≤
                  |((Real.sqrt (n + 1 : ℝ))⁻¹ * t) *
                    (Y i.val -
                      empiricalMean (fun j : Fin (n + 1) => Y j.val))|}
              (fun i =>
                (Y i.val -
                  empiricalMean (fun j : Fin (n + 1) => Y j.val)) ^ 2) i
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))) := by
  classical
  let P : Measure (Fin (n + 1)) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
  let Z : Fin (n + 1) → ℝ :=
    fun i => Y i.val - empiricalMean (fun j : Fin (n + 1) => Y j.val)
  let u : ℝ := (Real.sqrt (n + 1 : ℝ))⁻¹ * t
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let C : ℝ := 2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2
  let tail : Fin (n + 1) → ℝ :=
    fun i => Set.indicator {i : Fin (n + 1) | δ ≤ |u * Z i|}
      (fun i => (Z i) ^ 2) i
  change
    N *
        ‖centeredEmpiricalCharFunFinSucc Y n u -
          (1 +
            scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
              complexInvNatSucc n)‖ ≤
      η * t ^ 2 * empiricalVarianceFinSucc Y n +
        C * t ^ 2 * ∫ i : Fin (n + 1), tail i ∂P
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hNnonneg : 0 ≤ N := hNpos.le
  have hsecond :
      ∫ i, (Z i) ^ 2 ∂P = empiricalVarianceFinSucc Y n := by
    simpa [P, Z, empiricalVarianceFinSucc] using
      integral_sq_sub_empiricalMean_uniformOn_univ_eq_variance
        (Y := fun j : Fin (n + 1) => Y j.val)
  have hu2_real : u ^ 2 = t ^ 2 * N⁻¹ := by
    have hsqrt_sq :
        Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    dsimp [u, N]
    norm_num [Nat.cast_add]
    rw [mul_pow]
    rw [show (Real.sqrt ((n : ℝ) + 1))⁻¹ ^ 2 = ((n : ℝ) + 1)⁻¹ by
      have hNne : (n : ℝ) + 1 ≠ 0 := by positivity
      have hsqrt_ne' : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
        exact (Real.sqrt_pos.2 (by positivity)).ne'
      field_simp [hsqrt_ne', hNne]
      rw [hsqrt_sq]]
    ring
  have hNu2 : N * u ^ 2 = t ^ 2 := by
    rw [hu2_real]
    field_simp [hNpos.ne']
  have hbound :=
    centeredEmpiricalCharFunFinSucc_remainder_norm_le_integral_split
      (Y := Y) (n := n) (t := t) (δ := δ) (η := η) hδ hη hsmall
  change
    ‖centeredEmpiricalCharFunFinSucc Y n u -
        (1 +
          scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
            complexInvNatSucc n)‖ ≤
      ∫ i : Fin (n + 1),
        η * (u * Z i) ^ 2 +
          C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i)
        ∂P at hbound
  have htail_fun :
      (fun i : Fin (n + 1) =>
          Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i)) =
        fun i : Fin (n + 1) => u ^ 2 * tail i := by
    funext i
    dsimp [tail]
    by_cases hi : δ ≤ |u * Z i|
    · have hmem_real : u * Z i ∈ {y : ℝ | δ ≤ |y|} := hi
      have hmem_tail : i ∈ {i : Fin (n + 1) | δ ≤ |u * Z i|} := hi
      rw [Set.indicator_of_mem hmem_real, Set.indicator_of_mem hmem_tail]
      ring
    · have hnot_real : u * Z i ∉ {y : ℝ | δ ≤ |y|} := hi
      have hnot_tail : i ∉ {i : Fin (n + 1) | δ ≤ |u * Z i|} := hi
      rw [Set.indicator_of_notMem hnot_real, Set.indicator_of_notMem hnot_tail]
      ring
  have hsmall_fun :
      (fun i : Fin (n + 1) => η * (u * Z i) ^ 2) =
        fun i : Fin (n + 1) => (η * u ^ 2) * (Z i) ^ 2 := by
    funext i
    ring
  have hsmall_int :
      ∫ i : Fin (n + 1), η * (u * Z i) ^ 2 ∂P =
        η * u ^ 2 * empiricalVarianceFinSucc Y n := by
    rw [hsmall_fun, integral_const_mul, hsecond]
  have htail_int :
      ∫ i : Fin (n + 1),
          C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i)
          ∂P =
        C * u ^ 2 * ∫ i : Fin (n + 1), tail i ∂P := by
    have hfun :
        (fun i : Fin (n + 1) =>
            C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i)) =
          fun i : Fin (n + 1) => (C * u ^ 2) * tail i := by
      funext i
      have hi_eq := congr_fun htail_fun i
      rw [hi_eq]
      ring
    rw [hfun, integral_const_mul]
  have hsum_int :
      ∫ i : Fin (n + 1),
          η * (u * Z i) ^ 2 +
            C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i)
          ∂P =
        η * u ^ 2 * empiricalVarianceFinSucc Y n +
          C * u ^ 2 * ∫ i : Fin (n + 1), tail i ∂P := by
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      hsmall_int, htail_int]
  calc
    N *
        ‖centeredEmpiricalCharFunFinSucc Y n u -
          (1 +
            scalarGaussianCharFunExponent t (empiricalVarianceFinSucc Y n) *
              complexInvNatSucc n)‖ ≤
        N *
          ∫ i : Fin (n + 1),
            η * (u * Z i) ^ 2 +
              C * Set.indicator {y : ℝ | δ ≤ |y|} (fun y => y ^ 2) (u * Z i)
            ∂P :=
        mul_le_mul_of_nonneg_left hbound hNnonneg
    _ = η * t ^ 2 * empiricalVarianceFinSucc Y n +
        C * t ^ 2 * ∫ i : Fin (n + 1), tail i ∂P := by
          rw [hsum_int]
          rw [← hNu2]
          ring

private theorem isLittleO_complexInvNatSucc_of_natSucc_mul_norm_tendsto_zero
    {R : ℕ → ℂ}
    (hR : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖R n‖) atTop (𝓝 0)) :
    R =o[atTop] fun n : ℕ => complexInvNatSucc n := by
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  filter_upwards [hR.eventually (gt_mem_nhds hc)] with n hn
  have hNpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hnorm_inv :
      ‖complexInvNatSucc n‖ = (((n + 1 : ℕ) : ℝ))⁻¹ := by
    have hnat :
        ‖(((n + 1 : ℕ) : ℂ))‖ = (((n + 1 : ℕ) : ℝ)) := by
      simpa using Complex.norm_natCast (n + 1)
    calc
      ‖complexInvNatSucc n‖ = ‖(((n + 1 : ℕ) : ℂ))⁻¹‖ := by
        simp [complexInvNatSucc, Nat.succ_eq_add_one]
      _ = ‖(((n + 1 : ℕ) : ℂ))‖⁻¹ := norm_inv _
      _ = (((n + 1 : ℕ) : ℝ))⁻¹ := by rw [hnat]
  have hlt_div : ‖R n‖ < c / (((n + 1 : ℕ) : ℝ)) := by
    rw [lt_div_iff₀ hNpos]
    simpa [mul_comm] using hn
  calc
    ‖R n‖ ≤ c * (((n + 1 : ℕ) : ℝ))⁻¹ := by
      simpa [div_eq_mul_inv] using le_of_lt hlt_div
    _ = c * ‖complexInvNatSucc n‖ := by rw [hnorm_inv]

/-- Diagonal empirical characteristic-function remainder from a scaled norm
estimate.

This deterministic bridge is the norm-estimate face of the Taylor remainder
premise used in the changing-support empirical characteristic-function power
argument: it is enough to show that `n+1` times the norm of the displayed
second-order remainder tends to zero. -/
private theorem centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_scaled_norm_tendsto_zero
    (Y : ℕ → ℝ) (u : ℝ)
    (hscaled :
      Tendsto
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) *
            ‖centeredEmpiricalCharFunFinSucc Y n
                ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
              (1 +
                scalarGaussianCharFunExponent u
                    (empiricalVarianceFinSucc Y n) *
                  complexInvNatSucc n)‖)
        atTop (𝓝 0)) :
    ((fun n : ℕ =>
        centeredEmpiricalCharFunFinSucc Y n ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
          (1 +
            scalarGaussianCharFunExponent u (empiricalVarianceFinSucc Y n) *
              complexInvNatSucc n)) =o[atTop]
      (fun n : ℕ => complexInvNatSucc n)) :=
  isLittleO_complexInvNatSucc_of_natSucc_mul_norm_tendsto_zero hscaled

/-- Diagonal empirical characteristic-function remainder from bounded
empirical variance and centered Lindeberg tails.

This deterministic constructor discharges the explicit Taylor-remainder
premise used by the changing-support characteristic-function bridge once the
empirical variances are eventually bounded and every centered scaled square
tail tends to zero. -/
private theorem
    centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_variance_bound_tail
    (Y : ℕ → ℝ) (u : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hvar_bound : ∀ᶠ n in atTop, empiricalVarianceFinSucc Y n ≤ B)
    (htail : ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc Y n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ)
        atTop (𝓝 0)) :
    ((fun n : ℕ =>
        centeredEmpiricalCharFunFinSucc Y n ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
          (1 +
            scalarGaussianCharFunExponent u (empiricalVarianceFinSucc Y n) *
              complexInvNatSucc n)) =o[atTop]
      (fun n : ℕ => complexInvNatSucc n)) := by
  refine
    centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_scaled_norm_tendsto_zero
      (Y := Y) (u := u) ?_
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards with n
    have hnonneg :
        0 ≤ ((n + 1 : ℕ) : ℝ) *
          ‖centeredEmpiricalCharFunFinSucc Y n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
            (1 +
              scalarGaussianCharFunExponent u (empiricalVarianceFinSucc Y n) *
                complexInvNatSucc n)‖ :=
      mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    linarith
  · intro a ha
    let D : ℝ := u ^ 2 * B
    have hD_nonneg : 0 ≤ D := by
      dsimp [D]
      exact mul_nonneg (sq_nonneg u) hB
    let η : ℝ := a / (4 * (D + 1))
    have hη_pos : 0 < η := by
      dsimp [η]
      positivity
    rcases complex_exp_I_sub_quadratic_norm_le_eta_mul_sq_near_zero hη_pos with
      ⟨δ, hδ, hsmall⟩
    let C : ℝ := 2 * δ⁻¹ ^ 2 + δ⁻¹ + 1 / 2
    let K : ℝ := C * u ^ 2
    have htailK :
        Tendsto
          (fun n : ℕ =>
            K *
              centeredEmpiricalTailSqFinSucc Y n
                ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ)
          atTop (𝓝 0) := by
      simpa [K] using tendsto_const_nhds.mul (htail δ hδ)
    have htail_event :
        ∀ᶠ n in atTop,
          K *
              centeredEmpiricalTailSqFinSucc Y n
                ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ <
            a / 2 :=
      htailK.eventually (Iio_mem_nhds (half_pos ha))
    filter_upwards [hvar_bound, htail_event] with n hvarn htailn
    have hle :=
      centeredEmpiricalCharFunFinSucc_remainder_scaled_norm_le
        (Y := Y) (n := n) (t := u) (δ := δ) (η := η) hδ hη_pos.le hsmall
    change
      ((n + 1 : ℕ) : ℝ) *
          ‖centeredEmpiricalCharFunFinSucc Y n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
            (1 +
              scalarGaussianCharFunExponent u (empiricalVarianceFinSucc Y n) *
                complexInvNatSucc n)‖ ≤
        η * u ^ 2 * empiricalVarianceFinSucc Y n +
          C * u ^ 2 *
            centeredEmpiricalTailSqFinSucc Y n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ at hle
    have hvar_scaled_le : u ^ 2 * empiricalVarianceFinSucc Y n ≤ D := by
      dsimp [D]
      exact mul_le_mul_of_nonneg_left hvarn (sq_nonneg u)
    have hsmall_le_D :
        η * u ^ 2 * empiricalVarianceFinSucc Y n ≤ η * D := by
      calc
        η * u ^ 2 * empiricalVarianceFinSucc Y n =
            η * (u ^ 2 * empiricalVarianceFinSucc Y n) := by ring
        _ ≤ η * D := mul_le_mul_of_nonneg_left hvar_scaled_le hη_pos.le
    have hηD_le : η * D ≤ a / 4 := by
      have hD1pos : 0 < D + 1 := by positivity
      have hfrac : D / (D + 1) ≤ 1 := by
        rw [div_le_one hD1pos]
        linarith
      have heq : η * D = (a / 4) * (D / (D + 1)) := by
        dsimp [η]
        field_simp [hD1pos.ne']
      rw [heq]
      calc
        (a / 4) * (D / (D + 1)) ≤ (a / 4) * 1 := by
          exact mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = a / 4 := by ring
    have hsmall_le : η * u ^ 2 * empiricalVarianceFinSucc Y n ≤ a / 4 :=
      hsmall_le_D.trans hηD_le
    have htail_lt :
        C * u ^ 2 *
            centeredEmpiricalTailSqFinSucc Y n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ <
          a / 2 := by
      simpa [K, mul_assoc] using htailn
    calc
      ((n + 1 : ℕ) : ℝ) *
          ‖centeredEmpiricalCharFunFinSucc Y n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
            (1 +
              scalarGaussianCharFunExponent u (empiricalVarianceFinSucc Y n) *
                complexInvNatSucc n)‖ ≤
          η * u ^ 2 * empiricalVarianceFinSucc Y n +
            C * u ^ 2 *
              centeredEmpiricalTailSqFinSucc Y n
                ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ := hle
      _ < a := by nlinarith

/-- Diagonal empirical characteristic-function remainder from empirical
variance convergence and centered Lindeberg tails.

This is the chapter-facing deterministic form used after the projected
empirical variance has been identified: convergence of that variance supplies
the eventual bound required by
`centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_variance_bound_tail`. -/
theorem
    centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_variance_tendsto_tail
    (Y : ℕ → ℝ) {σ2 : ℝ}
    (hvar : Tendsto (fun n : ℕ => empiricalVarianceFinSucc Y n) atTop (𝓝 σ2))
    (u : ℝ)
    (htail : ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc Y n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ)
        atTop (𝓝 0)) :
    ((fun n : ℕ =>
        centeredEmpiricalCharFunFinSucc Y n ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
          (1 +
            scalarGaussianCharFunExponent u (empiricalVarianceFinSucc Y n) *
              complexInvNatSucc n)) =o[atTop]
      (fun n : ℕ => complexInvNatSucc n)) := by
  let B : ℝ := |σ2| + 1
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hvar_bound : ∀ᶠ n in atTop, empiricalVarianceFinSucc Y n ≤ B := by
    have hball :
        Metric.ball σ2 (1 : ℝ) ∈ 𝓝 σ2 :=
      Metric.ball_mem_nhds _ zero_lt_one
    filter_upwards [hvar.eventually hball] with n hn
    have habs : |empiricalVarianceFinSucc Y n - σ2| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    have hupper : empiricalVarianceFinSucc Y n - σ2 < 1 :=
      (abs_lt.1 habs).2
    have hσ_le_abs : σ2 ≤ |σ2| := le_abs_self σ2
    dsimp [B]
    linarith
  exact
    centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_variance_bound_tail
      (Y := Y) (u := u) hB hvar_bound htail

/-- Diagonal changing-support characteristic-function power bridge for the
ordinary `Fin (n+1)` empirical law.

If the empirical one-draw variance converges and the centered empirical
one-draw characteristic function has the displayed second-order Taylor
remainder at the `1 / sqrt (n+1)` scale, then the `n+1`-draw power converges to
the Gaussian characteristic function with the limiting variance scale.  This is
the theorem-facing reduction needed before discharging the Taylor remainder
from iid finite-second-moment assumptions in Hansen Theorem 10.4. -/
theorem
    centeredEmpiricalCharFunFinSucc_inv_sqrt_succ_pow_tendsto_of_variance_tendsto
    (Y : ℕ → ℝ) {σ2 : ℝ}
    (hvar : Tendsto (fun n : ℕ => empiricalVarianceFinSucc Y n) atTop (𝓝 σ2))
    (u : ℝ)
    (hrem :
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc Y n ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
            (1 +
              scalarGaussianCharFunExponent u (empiricalVarianceFinSucc Y n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n))) :
    Tendsto
      (fun n : ℕ =>
        centeredEmpiricalCharFunFinSucc Y n ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) ^
          Nat.succ n)
      atTop
      (𝓝 (Complex.exp (scalarGaussianCharFunExponent u σ2))) := by
  let A : ℕ → ℂ := fun n =>
    scalarGaussianCharFunExponent u (empiricalVarianceFinSucc Y n)
  have hVC :
      Tendsto (fun n : ℕ => (empiricalVarianceFinSucc Y n : ℂ)) atTop
        (𝓝 (σ2 : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto σ2).comp hvar
  have hA :
      Tendsto A atTop (𝓝 (scalarGaussianCharFunExponent u σ2)) := by
    have hmul :
        Tendsto
          (fun n : ℕ => (u : ℂ) ^ 2 * (empiricalVarianceFinSucc Y n : ℂ))
          atTop (𝓝 ((u : ℂ) ^ 2 * (σ2 : ℂ))) :=
      tendsto_const_nhds.mul hVC
    exact (hmul.div_const (2 : ℂ)).neg
  exact
    complex_tendsto_pow_succ_exp_of_isLittleO_sub_add_div_tendsto
      (f := fun n : ℕ =>
        centeredEmpiricalCharFunFinSucc Y n ((Real.sqrt (n + 1 : ℝ))⁻¹ * u))
      (a := A) (t := scalarGaussianCharFunExponent u σ2) hA
      (by
        simpa [A, complexInvNatSucc, one_div, div_eq_mul_inv, Nat.succ_eq_add_one]
          using hrem)

omit [Fintype ι] in
/-- Scalar variance of the ordinary finite nonparametric bootstrap sample mean.

This is the scalar form of Hansen equation (10.13): the conditional variance
of the bootstrap sample mean is the empirical one-draw variance divided by the
number of bootstrap draws. -/
theorem variance_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_mul
    {κ : Type*} [Fintype κ] [Nonempty κ] [Finite ι] [Nonempty ι]
    (Y : ι → ℝ) :
    Var[fun ωs : κ → ι => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs;
        (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))] =
      (Fintype.card κ : ℝ)⁻¹ *
        Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let c : ℝ := (Fintype.card κ : ℝ)⁻¹
  have hPκ : Pκ = Measure.pi (fun _ : κ => Pι) := by
    simpa [Pκ, Pι] using
      (ProbabilityTheory.uniformOn_pi (Ω := ι) (ι := κ)
        (f := fun _ : κ => (Set.univ : Set ι)))
  have hmem : ∀ t : κ, MemLp Y 2 Pι := fun _ =>
    memLp_two_uniformOn_univ (Y := Y)
  have hvarsum :
      Var[(∑ t, fun ωs : κ → ι => Y (ωs t)); Measure.pi (fun _ : κ => Pι)] =
        ∑ _t : κ, Var[Y; Pι] := by
    simpa using
      (ProbabilityTheory.variance_sum_pi
        (Ω := fun _ : κ => ι) (μ := fun _ : κ => Pι)
        (X := fun _ : κ => Y) hmem)
  have hsumvar :
      (∑ _t : κ, Var[Y; Pι]) = (Fintype.card κ : ℝ) * Var[Y; Pι] := by
    simp
  have hsample :
      (fun ωs : κ → ι =>
          empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs) =
        fun ωs : κ → ι => c * (∑ t, fun ωs : κ → ι => Y (ωs t)) ωs := by
    ext ωs
    simp [empiricalBootstrapResampleMean, c]
  calc
    Var[fun ωs : κ → ι => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs; Pκ]
        = Var[fun ωs : κ → ι => c * (∑ t, fun ωs : κ → ι => Y (ωs t)) ωs; Pκ] := by
          rw [hsample]
    _ = Var[fun ωs : κ → ι => c * (∑ t, fun ωs : κ → ι => Y (ωs t)) ωs;
          Measure.pi (fun _ : κ => Pι)] := by
          rw [hPκ]
    _ = c ^ 2 * Var[(∑ t, fun ωs : κ → ι => Y (ωs t));
          Measure.pi (fun _ : κ => Pι)] := by
          rw [ProbabilityTheory.variance_const_mul]
    _ = c ^ 2 * ((Fintype.card κ : ℝ) * Var[Y; Pι]) := by
          rw [hvarsum, hsumvar]
    _ = (Fintype.card κ : ℝ)⁻¹ * Var[Y; Pι] := by
          have hcard : (Fintype.card κ : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr Fintype.card_ne_zero
          dsimp [c]
          field_simp [hcard]

/-- Scalar covariance scale for the normalized ordinary nonparametric-bootstrap
sample mean.

Multiplying the centered resample mean by `sqrt (#κ)` exactly restores the
one-draw empirical variance.  This is the scalar finite-sample covariance
identity behind Hansen's bootstrap CLT normalization. -/
theorem variance_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    Var[fun ωs : κ → ι =>
        Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y);
        (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))] =
      Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : (κ → ι) → ℝ :=
    fun ωs => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs
  have hX_meas : AEStronglyMeasurable X Pκ :=
    AEStronglyMeasurable.of_discrete
  have hvar_center :
      Var[fun ωs : κ → ι => X ωs - empiricalMean Y; Pκ] =
        Var[X; Pκ] := by
    exact ProbabilityTheory.variance_sub_const hX_meas (empiricalMean Y)
  have hbase :
      Var[X; Pκ] =
        (Fintype.card κ : ℝ)⁻¹ *
          Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
    simpa [X, Pκ] using
      variance_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_mul
        (κ := κ) (Y := Y)
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_sq :
      Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
    Real.sq_sqrt hcard_pos.le
  calc
    Var[fun ωs : κ → ι =>
        Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y); Pκ]
        = Real.sqrt (Fintype.card κ : ℝ) ^ 2 *
            Var[fun ωs : κ → ι => X ωs - empiricalMean Y; Pκ] := by
          rw [ProbabilityTheory.variance_const_mul]
    _ = Real.sqrt (Fintype.card κ : ℝ) ^ 2 * Var[X; Pκ] := by
          rw [hvar_center]
    _ = Real.sqrt (Fintype.card κ : ℝ) ^ 2 *
          ((Fintype.card κ : ℝ)⁻¹ *
            Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)]) := by
          rw [hbase]
    _ = Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
          rw [hsqrt_sq]
          field_simp [hcard_pos.ne']

/-- Scalar raw second moment of the normalized ordinary
nonparametric-bootstrap sample mean.

Since `sqrt (#κ) (Ybar* - Ybar)` has exact conditional mean zero, its raw
second moment is the empirical one-draw variance. -/
theorem integral_sq_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq_variance
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
            empiricalMean Y)) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let Z : (κ → ι) → ℝ :=
    fun ωs =>
      Real.sqrt (Fintype.card κ : ℝ) *
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs -
          empiricalMean Y)
  have hmean : ∫ ωs, Z ωs ∂Pκ = 0 := by
    simpa [Z, Pκ, smul_eq_mul] using
      integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero
        (κ := κ) (Y := Y)
  have hvar : Var[Z; Pκ] = Var[Y; Pι] := by
    simpa [Z, Pκ, Pι] using
      variance_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq
        (κ := κ) (Y := Y)
  change ∫ ωs, Z ωs ^ 2 ∂Pκ = Var[Y; Pι]
  calc
    ∫ ωs, Z ωs ^ 2 ∂Pκ =
        ∫ ωs, (Z ωs - ∫ ωs, Z ωs ∂Pκ) ^ 2 ∂Pκ := by
          rw [hmean]
          simp
    _ = Var[Z; Pκ] := by
          exact (ProbabilityTheory.variance_eq_integral
            (AEStronglyMeasurable.of_discrete :
              AEStronglyMeasurable Z Pκ).aemeasurable).symm
    _ = Var[Y; Pι] := hvar

/-- Centered second moment of the ordinary finite nonparametric bootstrap
sample mean.

This is Hansen equation (10.13) in the exact second-moment form used by the
bootstrap WLLN proof. -/
theorem integral_sq_resampleMean_sub_empiricalMean_eq_inv_card_mul_variance
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      (Fintype.card κ : ℝ)⁻¹ *
        Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : (κ → ι) → ℝ :=
    fun ωs => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs
  have hmean : ∫ ωs, X ωs ∂Pκ = empiricalMean Y := by
    simpa [X, Pκ] using
      integral_empiricalBootstrapResampleMean_uniformOn_fun_eq_empiricalMean
        (κ := κ) (Y := Y)
  have hX_meas : AEMeasurable X Pκ :=
    (measurable_of_finite X).aemeasurable
  calc
    ∫ ωs : κ → ι, (X ωs - empiricalMean Y) ^ 2 ∂Pκ =
        ∫ ωs : κ → ι, (X ωs - ∫ ωs, X ωs ∂Pκ) ^ 2 ∂Pκ := by
          rw [hmean]
    _ = Var[X; Pκ] := (ProbabilityTheory.variance_eq_integral hX_meas).symm
    _ = (Fintype.card κ : ℝ)⁻¹ *
        Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
          simpa [X, Pκ] using
            (variance_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_mul
              (κ := κ) (Y := Y))

/-- Scalar second-moment bound for the ordinary finite nonparametric bootstrap
sample mean.

The centered bootstrap sample mean has conditional second moment bounded by
`1 / #κ` times the empirical raw second moment of one draw.  When the resample
size and empirical support have the same cardinality, this is the scalar
`n^{-2} ∑ Y_i^2` bound used in Hansen's proof of Theorem 10.2. -/
theorem integral_sq_resampleMean_sub_empiricalMean_le_inv_card_mul_secondMoment
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) ≤
      (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i ^ 2) := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have hvar_le :
      Var[Y; Pι] ≤ ∫ i, Y i ^ 2 ∂Pι :=
    ProbabilityTheory.variance_le_expectation_sq
      (μ := Pι) (X := Y) (AEStronglyMeasurable.of_discrete)
  have hsecond :
      ∫ i, Y i ^ 2 ∂Pι =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i ^ 2 := by
    simpa [Pι] using
      (integral_uniformOn_univ_eq_card_inv_smul_sum (E := ℝ)
        (fun i => Y i ^ 2))
  have hc_nonneg : 0 ≤ (Fintype.card κ : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    ∫ ωs : κ → ι,
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
        = (Fintype.card κ : ℝ)⁻¹ * Var[Y; Pι] := by
          simpa [Pι] using
            (integral_sq_resampleMean_sub_empiricalMean_eq_inv_card_mul_variance
              (κ := κ) (Y := Y))
    _ ≤ (Fintype.card κ : ℝ)⁻¹ * ∫ i, Y i ^ 2 ∂Pι :=
          mul_le_mul_of_nonneg_left hvar_le hc_nonneg
    _ = (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i ^ 2) := by
          rw [hsecond]

/-- Finite-dimensional empirical covariance identity for one bootstrap draw.

This is the matrix form of Hansen's exact bootstrap covariance formula
(10.11): under uniform resampling from a finite empirical support, the
covariance matrix is the average outer product of deviations from the empirical
mean. -/
theorem covMat_uniformOn_univ_eq_card_inv_smul_sum_centered
    {k : Type*} (Y : ι → k → ℝ) :
    covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y =
      fun a b =>
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
          ∑ i, (Y i a -
              ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j a) *
            (Y i b -
              ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j b) := by
  ext a b
  have hmean_a :
      ∫ i, Y i a ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j a :=
    integral_uniformOn_univ_eq_card_inv_smul_sum (fun i => Y i a)
  have hmean_b :
      ∫ i, Y i b ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j b :=
    integral_uniformOn_univ_eq_card_inv_smul_sum (fun i => Y i b)
  simp [covMat, ProbabilityTheory.covariance, hmean_a, hmean_b,
    integral_uniformOn_univ_eq_card_inv_smul_sum]

omit [Fintype ι] in
/-- Covariance matrix of the ordinary finite nonparametric bootstrap sample mean.

This is the finite-dimensional form of Hansen equation (10.13): the
conditional covariance matrix of the bootstrap sample mean is the empirical
one-draw covariance matrix divided by the number of bootstrap draws. -/
theorem covMat_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_smul
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) :
    covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
        (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a) =
      (Fintype.card κ : ℝ)⁻¹ •
        covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let Pprod : Measure (κ → ι) := Measure.pi (fun _ : κ => Pι)
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Z : κ → (κ → ι) → k → ℝ := fun t ωs a => Y (ωs t) a
  let c : ℝ := (Fintype.card κ : ℝ)⁻¹
  let j : κ := Classical.choice ‹Nonempty κ›
  have hPκ : Pκ = Pprod := by
    simpa [Pκ, Pprod, Pι] using
      (ProbabilityTheory.uniformOn_pi (Ω := ι) (ι := κ)
        (f := fun _ : κ => (Set.univ : Set ι)))
  have hsample :
      (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a) =
        fun ωs a => c * ∑ t, Z t ωs a := by
    ext ωs a
    simp [empiricalBootstrapResampleMean, Z, c]
  have hZ : ∀ t a, MemLp (fun ωs => Z t ωs a) 2 Pprod := by
    intro t a
    exact ⟨AEStronglyMeasurable.of_discrete, eLpNorm_lt_top_of_finite⟩
  have hiind :
      iIndepFun (fun t (ωs : κ → ι) => ωs t) Pprod := by
    simpa [Pprod] using
      (ProbabilityTheory.iIndepFun_pi
        (μ := fun _ : κ => Pι) (X := fun _ : κ => id)
        (fun _ => aemeasurable_id))
  have hindep :
      ∀ a b, Pairwise (fun t u =>
        (fun ωs => Z t ωs a) ⟂ᵢ[Pprod] (fun ωs => Z u ωs b)) := by
    intro a b t u htu
    exact IndepFun.comp (hiind.indepFun htu)
      (measurable_of_finite (fun i => Y i a))
      (measurable_of_finite (fun i => Y i b))
  have hcov_eval :
      ∀ t, covMat Pprod (Z t) = covMat Pι Y := by
    intro t
    ext a b
    have hmap : Pprod.map (Function.eval t) = Pι :=
      (measurePreserving_eval (μ := fun _ : κ => Pι) t).map_eq
    have hcov :=
      ProbabilityTheory.covariance_map_fun
        (μ := Pprod) (Z := Function.eval t)
        (X := fun i => Y i a) (Y := fun i => Y i b)
        (AEStronglyMeasurable.of_discrete)
        (AEStronglyMeasurable.of_discrete)
        (measurable_pi_apply t).aemeasurable
    calc
      cov[fun ωs => Z t ωs a, fun ωs => Z t ωs b; Pprod]
          = cov[fun i => Y i a, fun i => Y i b; Pprod.map (Function.eval t)] := by
            simpa [Z, Function.comp_def] using hcov.symm
      _ = cov[fun i => Y i a, fun i => Y i b; Pι] := by
            rw [hmap]
  have hcov :
      ∀ t a b,
        cov[fun ωs => Z t ωs a, fun ωs => Z t ωs b; Pprod] =
          cov[fun ωs => Z j ωs a, fun ωs => Z j ωs b; Pprod] := by
    intro t a b
    have ht := congrFun (congrFun (hcov_eval t) a) b
    have hj := congrFun (congrFun (hcov_eval j) a) b
    simpa [covMat] using ht.trans hj.symm
  have hsample_cov :
      covMat Pprod (fun ωs a => c * ∑ t, Z t ωs a) =
        c • covMat Pprod (Z j) := by
    simpa [c] using
      (iidSampleMean_covMat_eq_inv_card_smul
        (μ := Pprod) (Z := Z) j hZ hindep hcov)
  calc
    covMat Pκ
        (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)
        = covMat Pprod
            (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a) := by
          rw [hPκ]
    _ = covMat Pprod (fun ωs a => c * ∑ t, Z t ωs a) := by
          rw [hsample]
    _ = c • covMat Pprod (Z j) := hsample_cov
    _ = c • covMat Pι Y := by
          rw [hcov_eval j]

/-- Matrix covariance scale for the normalized ordinary nonparametric-bootstrap
sample mean.

The covariance matrix of `sqrt (#κ) (Ybar* - Ybar)` under the finite uniform
resampling law is exactly the empirical one-draw covariance matrix.  This is
the finite-dimensional counterpart of
`variance_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq` and the
matrix form of Hansen's bootstrap CLT normalization calculation. -/
theorem covMat_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) :
    covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
        (fun ωs a =>
          Real.sqrt (Fintype.card κ : ℝ) *
            (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a -
              empiricalMean Y a)) =
      covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let X : (κ → ι) → k → ℝ :=
    fun ωs => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs
  have hbase :
      covMat Pκ X = (Fintype.card κ : ℝ)⁻¹ • covMat Pι Y := by
    simpa [X, Pκ, Pι] using
      covMat_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_smul
        (κ := κ) (Y := Y)
  have hcard_pos : 0 < (Fintype.card κ : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsqrt_sq :
      Real.sqrt (Fintype.card κ : ℝ) ^ 2 = (Fintype.card κ : ℝ) :=
    Real.sq_sqrt hcard_pos.le
  ext a b
  have hXa : Integrable (fun ωs => X ωs a) Pκ := Integrable.of_finite
  have hXb : Integrable (fun ωs => X ωs b) Pκ := Integrable.of_finite
  have hcenter :
      cov[fun ωs => X ωs a - empiricalMean Y a,
          fun ωs => X ωs b - empiricalMean Y b; Pκ] =
        cov[fun ωs => X ωs a, fun ωs => X ωs b; Pκ] := by
    rw [ProbabilityTheory.covariance_sub_const_left hXa,
      ProbabilityTheory.covariance_sub_const_right hXb]
  have hbase_ab := congrFun (congrFun hbase a) b
  have hbase_cov :
      cov[fun ωs => X ωs a, fun ωs => X ωs b; Pκ] =
        (Fintype.card κ : ℝ)⁻¹ * covMat Pι Y a b := by
    simpa [covMat, Matrix.smul_apply] using hbase_ab
  calc
    covMat Pκ
        (fun ωs a =>
          Real.sqrt (Fintype.card κ : ℝ) *
            (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a -
              empiricalMean Y a)) a b
        =
          Real.sqrt (Fintype.card κ : ℝ) ^ 2 *
            cov[fun ωs => X ωs a - empiricalMean Y a,
              fun ωs => X ωs b - empiricalMean Y b; Pκ] := by
          dsimp [covMat, X]
          rw [ProbabilityTheory.covariance_const_mul_left,
            ProbabilityTheory.covariance_const_mul_right]
          ring
    _ = Real.sqrt (Fintype.card κ : ℝ) ^ 2 *
          cov[fun ωs => X ωs a, fun ωs => X ωs b; Pκ] := by
          rw [hcenter]
    _ = Real.sqrt (Fintype.card κ : ℝ) ^ 2 *
          ((Fintype.card κ : ℝ)⁻¹ * covMat Pι Y a b) := by
          rw [hbase_cov]
    _ = covMat Pι Y a b := by
          rw [hsqrt_sq]
          field_simp [hcard_pos.ne']

omit [MeasurableSingletonClass ι] in
/-- Coordinate zero-mean identity for the normalized ordinary
nonparametric-bootstrap sample mean.

This is the coordinate face of
`integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero`,
stated in the matrix notation used by the finite-dimensional CLT path. -/
theorem integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_apply_sub_eq_zero
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) (a : k) :
    ∫ ωs : κ → ι,
        Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a -
            empiricalMean Y a)
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      0 := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Z : (κ → ι) → k → ℝ :=
    fun ωs =>
      Real.sqrt (Fintype.card κ : ℝ) •
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y)
  have hZ_int : Integrable Z Pκ := Integrable.of_finite
  have hzero : ∫ ωs, Z ωs ∂Pκ = 0 := by
    simpa [Z, Pκ] using
      integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero
        (κ := κ) (Y := Y)
  have hcoord : ∫ ωs, Z ωs a ∂Pκ = 0 := by
    rw [← integral_apply (μ := Pκ) (f := Z) hZ_int a, hzero]
    rfl
  simpa [Z, Pκ, Pi.smul_apply] using hcoord

/-- Raw cross-moment identity for the normalized ordinary
nonparametric-bootstrap sample mean.

Because the normalized centered resample mean has exact conditional mean zero,
its conditional cross moment equals its covariance.  Combined with
`covMat_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq`, this gives
the empirical covariance matrix as the exact finite-resample second moment of
the CLT-normalized bootstrap mean. -/
theorem integral_mul_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq_covMat
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) (a b : k) :
    ∫ ωs : κ → ι,
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a -
            empiricalMean Y a)) *
        (Real.sqrt (Fintype.card κ : ℝ) *
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs b -
            empiricalMean Y b))
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y a b := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let Z : (κ → ι) → k → ℝ :=
    fun ωs a =>
      Real.sqrt (Fintype.card κ : ℝ) *
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a -
          empiricalMean Y a)
  have hZa : MemLp (fun ωs : κ → ι => Z ωs a) 2 Pκ := by
    exact memLp_two_uniformOn_univ (ι := κ → ι) (E := ℝ)
      (Y := fun ωs : κ → ι => Z ωs a)
  have hZb : MemLp (fun ωs : κ → ι => Z ωs b) 2 Pκ := by
    exact memLp_two_uniformOn_univ (ι := κ → ι) (E := ℝ)
      (Y := fun ωs : κ → ι => Z ωs b)
  have hmean_a : ∫ ωs, Z ωs a ∂Pκ = 0 := by
    simpa [Z, Pκ] using
      integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_apply_sub_eq_zero
        (κ := κ) (Y := Y) a
  have hmean_b : ∫ ωs, Z ωs b ∂Pκ = 0 := by
    simpa [Z, Pκ] using
      integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_apply_sub_eq_zero
        (κ := κ) (Y := Y) b
  have hcov_raw :
      cov[fun ωs => Z ωs a, fun ωs => Z ωs b; Pκ] =
        ∫ ωs, Z ωs a * Z ωs b ∂Pκ := by
    rw [ProbabilityTheory.covariance_eq_sub hZa hZb, hmean_a, hmean_b]
    simp
  have hcov :
      cov[fun ωs => Z ωs a, fun ωs => Z ωs b; Pκ] =
        covMat Pι Y a b := by
    have hcovMat :=
      congrFun
        (congrFun
          (covMat_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq
            (κ := κ) (Y := Y)) a) b
    simpa [covMat, Z, Pκ, Pι] using hcovMat
  rw [← hcov_raw]
  exact hcov

/-- Euclidean raw second moment of the normalized ordinary
nonparametric-bootstrap sample mean.

The squared Euclidean norm of `sqrt (#κ) (Ybar* - Ybar)` has conditional
expectation equal to the trace of the empirical one-draw covariance matrix.
This is the finite-dimensional raw second-moment face of Hansen's bootstrap
CLT normalization. -/
theorem integral_norm_sq_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq_trace_covMat
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → EuclideanSpace ℝ k) :
    ∫ ωs : κ → ι,
        ‖Real.sqrt (Fintype.card κ : ℝ) •
          (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y)‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      Matrix.trace
        (covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)
          (fun i a => Y i a)) := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let Z : (κ → ι) → EuclideanSpace ℝ k :=
    fun ωs =>
      Real.sqrt (Fintype.card κ : ℝ) •
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y)
  have hmean : ∫ ωs, Z ωs ∂Pκ = 0 := by
    simpa [Z, Pκ] using
      integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero
        (κ := κ) (Y := Y)
  have htrace :
      Matrix.trace (covMat Pκ (fun ωs a => Z ωs a)) =
        Matrix.trace (covMat Pι (fun i a => Y i a)) := by
    have hcov :=
      covMat_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq
        (κ := κ) (Y := fun i a => Y i a)
    simpa [Z, Pκ, Pι, Pi.smul_apply, empiricalBootstrapResampleMean, empiricalMean] using
      congrArg Matrix.trace hcov
  change ∫ ωs, ‖Z ωs‖ ^ 2 ∂Pκ =
    Matrix.trace (covMat Pι (fun i a => Y i a))
  calc
    ∫ ωs, ‖Z ωs‖ ^ 2 ∂Pκ =
        ∫ ωs, ‖Z ωs - ∫ ωs, Z ωs ∂Pκ‖ ^ 2 ∂Pκ := by
          rw [hmean]
          simp
    _ = Matrix.trace (covMat Pκ (fun ωs a => Z ωs a)) := by
          exact integral_norm_sq_sub_mean_eq_trace_covMat_euclidean_of_finite
            (μ := Pκ) Z
    _ = Matrix.trace (covMat Pι (fun i a => Y i a)) := htrace

omit [Fintype ι] in
/-- Trace of the finite-dimensional nonparametric-bootstrap sample-mean
covariance matrix.

This is the trace form of Hansen equation (10.13). -/
theorem trace_covMat_resampleMean_eq_inv_card_mul
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) :
    Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) =
      (Fintype.card κ : ℝ)⁻¹ *
        Matrix.trace
          (covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y) := by
  rw [covMat_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_smul
    (κ := κ) (Y := Y)]
  simp [Matrix.trace_smul]

/-- The empirical one-draw covariance trace is bounded by the empirical raw
second moment.

This is the finite-dimensional trace inequality used after (10.13) in Hansen's
proof of Theorem 10.2. -/
theorem trace_covMat_uniformOn_univ_le_card_inv_smul_sum_sq
    {k : Type*} [Fintype k] [Nonempty ι] (Y : ι → k → ℝ) :
    Matrix.trace
        (covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y) ≤
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
        ∑ i, ∑ a, Y i a ^ 2 := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have htrace :
      Matrix.trace (covMat Pι Y) = ∑ a, Var[fun i => Y i a; Pι] := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    exact ProbabilityTheory.covariance_self
      (AEStronglyMeasurable.of_discrete : AEStronglyMeasurable (fun i => Y i a) Pι).aemeasurable
  have hvar_le :
      ∀ a, Var[fun i => Y i a; Pι] ≤ ∫ i, Y i a ^ 2 ∂Pι := by
    intro a
    exact ProbabilityTheory.variance_le_expectation_sq
      (μ := Pι) (X := fun i => Y i a) AEStronglyMeasurable.of_discrete
  have hintegral_sum :
      (∑ a, ∫ i, Y i a ^ 2 ∂Pι) =
        ∫ i, ∑ a, Y i a ^ 2 ∂Pι := by
    rw [integral_finset_sum]
    intro a _ha
    exact Integrable.of_finite
  have hsecond :
      ∫ i, ∑ a, Y i a ^ 2 ∂Pι =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
          ∑ i, ∑ a, Y i a ^ 2 := by
    simpa [Pι] using
      (integral_uniformOn_univ_eq_card_inv_smul_sum (E := ℝ)
        (fun i => ∑ a, Y i a ^ 2))
  calc
    Matrix.trace (covMat Pι Y)
        = ∑ a, Var[fun i => Y i a; Pι] := htrace
    _ ≤ ∑ a, ∫ i, Y i a ^ 2 ∂Pι :=
          Finset.sum_le_sum fun a _ha => hvar_le a
    _ = ∫ i, ∑ a, Y i a ^ 2 ∂Pι := hintegral_sum
    _ = ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
          ∑ i, ∑ a, Y i a ^ 2 := hsecond

/-- Trace second-moment bound for the finite-dimensional nonparametric-bootstrap
sample mean.

When the resample size and empirical support have the same cardinality, this is
the vector trace version of Hansen's `n^{-2} ∑ Yᵢ'Yᵢ` bound in the proof of
Theorem 10.2. -/
theorem trace_covMat_resampleMean_le_inv_card_mul_secondMoment
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) :
    Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) ≤
      (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2) := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have htrace_eq :
      Matrix.trace
          (covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
            (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) =
        (Fintype.card κ : ℝ)⁻¹ * Matrix.trace (covMat Pι Y) := by
    simpa [Pι] using trace_covMat_resampleMean_eq_inv_card_mul (κ := κ) (Y := Y)
  have htrace_le :
      Matrix.trace (covMat Pι Y) ≤
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2 := by
    simpa [Pι] using trace_covMat_uniformOn_univ_le_card_inv_smul_sum_sq (Y := Y)
  have hc_nonneg : 0 ≤ (Fintype.card κ : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a))
        = (Fintype.card κ : ℝ)⁻¹ * Matrix.trace (covMat Pι Y) := htrace_eq
    _ ≤ (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2) :=
          mul_le_mul_of_nonneg_left htrace_le hc_nonneg

omit [MeasurableSingletonClass ι] in
/-- Expected squared Euclidean norm of the centered nonparametric-bootstrap
sample mean as a covariance trace. -/
theorem integral_norm_sq_resampleMean_sub_empiricalMean_eq_trace_covMat
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → EuclideanSpace ℝ k) :
    ∫ ωs : κ → ι,
        ‖empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : (κ → ι) → EuclideanSpace ℝ k :=
    fun ωs => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs
  have hmean : ∫ ωs, X ωs ∂Pκ = empiricalMean Y := by
    simpa [X, Pκ] using
      integral_empiricalBootstrapResampleMean_uniformOn_fun_eq_empiricalMean
        (κ := κ) (Y := Y)
  calc
    ∫ ωs : κ → ι, ‖X ωs - empiricalMean Y‖ ^ 2 ∂Pκ =
        ∫ ωs : κ → ι, ‖X ωs - ∫ ωs, X ωs ∂Pκ‖ ^ 2 ∂Pκ := by
          rw [hmean]
    _ = Matrix.trace (covMat Pκ (fun ωs a => X ωs a)) := by
          exact integral_norm_sq_sub_mean_eq_trace_covMat_euclidean_of_finite
            (μ := Pκ) X

/-- Finite-dimensional vector second-moment bound for the ordinary
nonparametric-bootstrap sample mean.

When the resample size and empirical support have the same cardinality, this
is Hansen's vector `n^{-2} ∑ Yᵢ'Yᵢ` bound in the proof of Theorem 10.2. -/
theorem integral_norm_sq_resampleMean_sub_empiricalMean_le_secondMoment
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → EuclideanSpace ℝ k) :
    ∫ ωs : κ → ι,
        ‖empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) ≤
      (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2) := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Ycoord : ι → k → ℝ := fun i a => Y i a
  have htrace :
      ∫ ωs : κ → ι,
          ‖empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y‖ ^ 2
          ∂Pκ =
        Matrix.trace (covMat Pκ
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) := by
    simpa [Pκ] using
      integral_norm_sq_resampleMean_sub_empiricalMean_eq_trace_covMat
        (κ := κ) (Y := Y)
  have htrace_bound :
      Matrix.trace (covMat Pκ
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) ≤
        (Fintype.card κ : ℝ)⁻¹ *
          (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Ycoord i a ^ 2) := by
    simpa [Pκ, Ycoord, empiricalBootstrapResampleMean] using
      trace_covMat_resampleMean_le_inv_card_mul_secondMoment
        (κ := κ) (Y := Ycoord)
  calc
    ∫ ωs : κ → ι,
        ‖empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y‖ ^ 2
        ∂Pκ
        = Matrix.trace (covMat Pκ
            (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) := htrace
    _ ≤ (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2) := by
          simpa [Ycoord] using htrace_bound

end EmpiricalDistribution

end HansenEconometrics
