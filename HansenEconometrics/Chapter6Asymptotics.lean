import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.CentralLimitTheorem
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 6 Asymptotics

This file collects chapter-facing large-sample theorem wrappers.  The current
public surface covers the iid scalar CLT, the finite-dimensional iid vector
CLT, and fixed/indexed Cramér-Wold endpoints for triangular-array CLTs, using
Mathlib's one-dimensional CLT plus the reusable Cramer-Wold bridges in
`AsymptoticUtils`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Real Topology ProbabilityTheory

namespace HansenEconometrics

open Matrix

section Consistency

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
variable [PseudoEMetricSpace E]

/-- **Hansen Definition 6.3, consistency.**

An estimator sequence is consistent for `θ` when it converges to the constant
limit `θ` in measure. This is a chapter-facing name for the Mathlib
`TendstoInMeasure` idiom used throughout the asymptotic files. -/
def Consistent (μ : Measure Ω) (θhat : ℕ → Ω → E) (θ : E) : Prop :=
  TendstoInMeasure μ θhat atTop (fun _ => θ)

/-- Unfolding lemma for the chapter-facing consistency definition. -/
theorem consistent_iff_tendstoInMeasure
    {μ : Measure Ω} {θhat : ℕ → Ω → E} {θ : E} :
    Consistent μ θhat θ ↔ TendstoInMeasure μ θhat atTop (fun _ => θ) :=
  Iff.rfl

/-- Projection from the chapter-facing consistency definition to the underlying
Mathlib convergence-in-measure statement. -/
theorem Consistent.tendstoInMeasure
    {μ : Measure Ω} {θhat : ℕ → Ω → E} {θ : E}
    (h : Consistent μ θhat θ) :
    TendstoInMeasure μ θhat atTop (fun _ => θ) :=
  h

end Consistency

section IidCLT

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
/-- Measurability of a fixed dot-product projection on finite-dimensional vectors. -/
private theorem measurable_dotProduct_right (a : k → ℝ) :
    Measurable (fun v : k → ℝ => v ⬝ᵥ a) := by
  classical
  simpa [dotProduct] using
    (continuous_finset_sum Finset.univ
      (fun i _ => (continuous_apply i).mul continuous_const)).measurable

omit [DecidableEq k] in
/-- A fixed dot-product projection of a square-integrable finite-dimensional vector is
square-integrable. -/
private theorem dotProduct_memLp_two
    {μ : Measure Ω} {Y : Ω → k → ℝ}
    (hY : MemLp Y 2 μ) (a : k → ℝ) :
    MemLp (fun ω => Y ω ⬝ᵥ a) 2 μ := by
  classical
  convert (memLp_finset_sum' (s := Finset.univ)
    (f := fun i ω => Y ω i * a i)
    (fun i _ => (hY.eval i).mul_const (a i))) using 1
  ext ω
  simp [dotProduct]

omit [DecidableEq k] in
/-- The covariance matrix of a square-integrable finite-dimensional vector is positive
semidefinite. -/
theorem covMat_posSemidef
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → k → ℝ}
    (hY : MemLp Y 2 μ) :
    (covMat μ Y).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian]
    ext i j
    simp [covMat, ProbabilityTheory.covariance_comm]
  · intro a
    have hvar := variance_dotProduct_eq_dotProduct_covMat_mulVec
      (μ := μ) (X := Y) a (fun i => hY.eval i)
    have hnonneg := ProbabilityTheory.variance_nonneg (fun ω => Y ω ⬝ᵥ a) μ
    rw [hvar] at hnonneg
    simpa using hnonneg

/-- **Chapter 6 vector CLT reduction by Cramér-Wold.**

If every fixed scalar projection of a finite-dimensional statistic converges to
the matching scalar projection of a centered multivariate Gaussian, then the
whole statistic converges to that multivariate Gaussian. This is the
chapter-facing endpoint used by iid and future triangular-array CLT wrappers. -/
theorem vectorCLT_tendstoInDistribution_multivariateGaussian_of_projections
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hT : ∀ n, AEMeasurable (T n) μ)
    (hproj : ∀ a : k → ℝ,
      TendstoInDistribution
        (fun n ω => T n ω ⬝ᵥ a)
        atTop
        (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
        (fun _ => μ)
        (multivariateGaussian 0 S)) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (T n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 S) := by
  refine cramerWold_tendstoInDistribution ?_ (by fun_prop) ?_
  · intro n
    exact (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).measurable.comp_aemeasurable (hT n)
  · intro t
    let a : k → ℝ := t.ofLp
    have hscalar := hproj a
    refine TendstoInDistribution.congr ?_ ?_ hscalar
    · intro n
      exact ae_of_all μ (fun ω => by
        change T n ω ⬝ᵥ a =
          inner ℝ t (WithLp.toLp 2 (T n ω))
        simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k)
          t.ofLp (T n ω)).symm)
    · exact ae_of_all (multivariateGaussian 0 S) (fun z => by
        change z.ofLp ⬝ᵥ a = inner ℝ t z
        simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k)
          t.ofLp z.ofLp).symm)

/-- **Chapter 6 indexed vector CLT reduction by Cramér-Wold.**

If every fixed scalar projection of a finite-dimensional statistic converges to
the matching scalar projection of a centered multivariate Gaussian, then the
whole statistic converges to that multivariate Gaussian. Unlike
`vectorCLT_tendstoInDistribution_multivariateGaussian_of_projections`, this
version allows the source probability space and law to vary with the sequence
index, matching ordinary bootstrap resampling spaces. -/
theorem vectorCLT_tendstoInDistribution_multivariateGaussian_of_projections_indexed
    {Ωrow : ℕ → Type*} [∀ n, MeasurableSpace (Ωrow n)]
    {P : ∀ n, Measure (Ωrow n)} [∀ n, IsProbabilityMeasure (P n)]
    {T : ∀ n, Ωrow n → k → ℝ} {S : Matrix k k ℝ}
    (hT : ∀ n, AEMeasurable (T n) (P n))
    (hproj : ∀ a : k → ℝ,
      TendstoInDistribution
        (fun n ω => T n ω ⬝ᵥ a)
        atTop
        (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
        P
        (multivariateGaussian 0 S)) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (T n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      P
      (multivariateGaussian 0 S) := by
  refine cramerWold_tendstoInDistribution_indexed ?_ (by fun_prop) ?_
  · intro n
    exact (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).measurable.comp_aemeasurable (hT n)
  · intro t
    let a : k → ℝ := t.ofLp
    have hscalar := hproj a
    refine TendstoInDistribution.congr ?_ ?_ hscalar
    · intro n
      exact ae_of_all (P n) (fun ω => by
        change T n ω ⬝ᵥ a =
          inner ℝ t (WithLp.toLp 2 (T n ω))
        simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k)
          t.ofLp (T n ω)).symm)
    · exact ae_of_all (multivariateGaussian 0 S) (fun z => by
        change z.ofLp ⬝ᵥ a = inner ℝ t z
        simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k)
          t.ofLp z.ofLp).symm)

/-- **Hansen Theorem 6.3, scalar iid CLT wrapper.**

For iid real random variables with finite second moment, the centered sample
sum scaled by `1 / sqrt n` converges in distribution to the Gaussian with the
matching variance. This is a chapter-facing name for Mathlib's scalar CLT. -/
theorem iidScalarCLT_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 Var[Y 0; μ].toNNReal) ν)
    (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ))⁻¹ * (∑ i ∈ Finset.range n, Y i ω - n * μ[Y 0]))
      atTop Z (fun _ => μ) ν :=
  ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hZ hY hindep hident

omit [DecidableEq k] in
/-- **Hansen Theorem 6.3, scalar projection of the iid vector CLT.**

For iid finite-dimensional vectors with finite second moment, every fixed
linear projection of the centered sample sum satisfies the scalar CLT with
variance `a'Va`, where `V` is the covariance matrix of one draw. -/
theorem iidVectorProjectionCLT_tendstoInDistribution_gaussian_cov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Y : ℕ → Ω → k → ℝ} (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (a : k → ℝ) {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (a ⬝ᵥ (covMat μ (Y 0) *ᵥ a)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ))⁻¹ *
          (∑ i ∈ Finset.range n, Y i ω ⬝ᵥ a - n * (meanVec μ (Y 0) ⬝ᵥ a)))
      atTop Z (fun _ => μ) ν := by
  have hdot_meas := measurable_dotProduct_right (k := k) a
  have hident_scalar : ∀ i,
      IdentDistrib (fun ω => Y i ω ⬝ᵥ a) (fun ω => Y 0 ω ⬝ᵥ a) μ μ := by
    intro i
    simpa [Function.comp_def] using (hident i).comp hdot_meas
  have hindep_scalar :
      iIndepFun (fun i ω => Y i ω ⬝ᵥ a) μ := by
    simpa [Function.comp_def] using
      hindep.comp (fun _ v => v ⬝ᵥ a) (fun _ => hdot_meas)
  have hmean :
      μ[fun ω => Y 0 ω ⬝ᵥ a] = meanVec μ (Y 0) ⬝ᵥ a := by
    exact integral_dotProduct_eq_meanVec_dotProduct
      (μ := μ) (X := Y 0) a (fun i => (hY.eval i).integrable (by norm_num))
  have hZ' : HasLaw Z
      (gaussianReal 0 Var[fun ω => Y 0 ω ⬝ᵥ a; μ].toNNReal) ν := by
    rw [variance_dotProduct_eq_dotProduct_covMat_mulVec
      (μ := μ) (X := Y 0) a (fun i => hY.eval i)]
    exact hZ
  have hclt := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := μ) (P' := ν) (X := fun i ω => Y i ω ⬝ᵥ a)
    (Y := Z) hZ' (dotProduct_memLp_two (μ := μ) hY a) hindep_scalar hident_scalar
  convert hclt using 2 with n ω
  rw [hmean]

/-- **Hansen Theorem 6.3, finite-dimensional iid vector CLT.**

For iid `k`-vectors with finite second moment, the centered sample sum scaled
by `1 / sqrt n` converges in distribution to the centered multivariate Gaussian
with covariance matrix `covMat μ (Y 0)`. The theorem is stated in
`EuclideanSpace` form so it can be consumed directly by Cramer-Wold and Gaussian
law infrastructure. -/
theorem iidVectorCLT_tendstoInDistribution_multivariateGaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → k → ℝ} (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        WithLp.toLp 2
          ((Real.sqrt (n : ℝ))⁻¹ •
            (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0))))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 (covMat μ (Y 0))) := by
  refine cramerWold_tendstoInDistribution ?_ (by fun_prop) ?_
  · intro n
    have hsum : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, Y i ω) μ :=
      Finset.aemeasurable_fun_sum (Finset.range n)
        (fun i _ => (hident i).aemeasurable_fst)
    have hcenter : AEMeasurable
        (fun ω => ∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0)) μ :=
      hsum.sub aemeasurable_const
    have hscaled : AEMeasurable
        (fun ω => (Real.sqrt (n : ℝ))⁻¹ •
          (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0))) μ :=
      hcenter.const_smul ((Real.sqrt (n : ℝ))⁻¹)
    exact (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).measurable.comp_aemeasurable
      hscaled
  · intro t
    let a : k → ℝ := t.ofLp
    have hLawDot := hasLaw_multivariateGaussian_zero_dotProduct
      (S := covMat μ (Y 0)) (covMat_posSemidef (μ := μ) hY) a
    have hLawDual : HasLaw
        (fun z : EuclideanSpace ℝ k =>
          (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ k) t) z)
        (gaussianReal 0 (a ⬝ᵥ (covMat μ (Y 0) *ᵥ a)).toNNReal)
        (multivariateGaussian 0 (covMat μ (Y 0))) := by
      refine hLawDot.congr (ae_of_all _ fun z => ?_)
      change inner ℝ t z = z.ofLp ⬝ᵥ a
      simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k) t.ofLp z.ofLp)
    have hscalar := iidVectorProjectionCLT_tendstoInDistribution_gaussian_cov
      (μ := μ) (ν := multivariateGaussian 0 (covMat μ (Y 0)))
      (Y := Y) hY hindep hident a hLawDual
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hscalar
    intro n
    exact ae_of_all μ (fun ω => by
      change (Real.sqrt (n : ℝ))⁻¹ *
          (∑ i ∈ Finset.range n, Y i ω ⬝ᵥ a - n * (meanVec μ (Y 0) ⬝ᵥ a)) =
        inner ℝ t
          (WithLp.toLp 2
            ((Real.sqrt (n : ℝ))⁻¹ •
              (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0))))
      calc
        (Real.sqrt (n : ℝ))⁻¹ *
              (∑ i ∈ Finset.range n, Y i ω ⬝ᵥ a -
                n * (meanVec μ (Y 0) ⬝ᵥ a)) =
            ((Real.sqrt (n : ℝ))⁻¹ •
              (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0))) ⬝ᵥ a := by
              rw [smul_dotProduct, sub_dotProduct, sum_dotProduct, smul_dotProduct,
                smul_eq_mul]
              simp
        _ = inner ℝ t
            (WithLp.toLp 2
              ((Real.sqrt (n : ℝ))⁻¹ •
                (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0)))) := by
              simpa [a] using
                (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := k) t.ofLp
                  ((Real.sqrt (n : ℝ))⁻¹ •
                    (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) • meanVec μ (Y 0)))).symm)

end IidCLT

section BestUnbiased

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Hansen Theorem 6.11, sample-mean sharpness face.**

For pairwise independent identically distributed square-integrable scalar
observations, the variance of the finite-sample average is `1 / n` times the
variance of one draw. This formalizes the sharp sample-mean variance identity
around Hansen's best-unbiased-estimation theorem; the full lower bound for
arbitrary unbiased estimators is a separate efficiency statement. -/
theorem iidSampleMean_variance_eq_inv_card_mul
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → ℝ} (j : ι)
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hindep : Pairwise (fun i j => Z i ⟂ᵢ[μ] Z j))
    (hident : ∀ i, IdentDistrib (Z i) (Z j) μ μ) :
    Var[fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω; μ] =
      (Fintype.card ι : ℝ)⁻¹ * Var[Z j; μ] := by
  classical
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hpair : Set.Pairwise (↑(Finset.univ : Finset ι) : Set ι)
      (fun i j => Z i ⟂ᵢ[μ] Z j) := by
    intro i _ j _ hij
    exact hindep hij
  have hvarsum := ProbabilityTheory.IndepFun.variance_sum
    (μ := μ) (X := Z) (s := Finset.univ)
    (fun i _ => hZ i) hpair
  have hsumvar :
      (∑ i, Var[Z i; μ]) = (Fintype.card ι : ℝ) * Var[Z j; μ] := by
    calc
      (∑ i, Var[Z i; μ]) = ∑ _i : ι, Var[Z j; μ] := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact (hident i).variance_eq
      _ = (Fintype.card ι : ℝ) * Var[Z j; μ] := by
        simp
  have hsample_eq :
      (fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω) =
        fun ω => c * (∑ i, Z i) ω := by
    ext ω
    simp [c]
  rw [hsample_eq]
  calc
    Var[fun ω => c * (∑ i, Z i) ω; μ]
        = c ^ 2 * Var[(∑ i, Z i); μ] := by
          rw [ProbabilityTheory.variance_const_mul]
    _ = c ^ 2 * (∑ i, Var[Z i; μ]) := by
          rw [hvarsum]
    _ = c ^ 2 * ((Fintype.card ι : ℝ) * Var[Z j; μ]) := by
          rw [hsumvar]
    _ = (Fintype.card ι : ℝ)⁻¹ * Var[Z j; μ] := by
          have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          dsimp [c]
          field_simp [hcard]

/-- **Hansen Theorem 6.11, scalar best-linear-unbiased face.**

Among linear unbiased estimators `∑ᵢ wᵢ Zᵢ` with weights summing to one, the
equal-weight sample mean has minimal variance under iid square-integrable scalar
observations. This is a linear-estimator lower-bound face of Hansen's
best-unbiased-estimation theorem; the arbitrary-estimator lower bound remains a
separate efficiency statement. -/
theorem iidLinearUnbiasedEstimator_variance_ge_sampleMean
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → ℝ} (j : ι) (w : ι → ℝ)
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hindep : Pairwise (fun i l => Z i ⟂ᵢ[μ] Z l))
    (hident : ∀ i, IdentDistrib (Z i) (Z j) μ μ)
    (hw : ∑ i, w i = 1) :
    (Fintype.card ι : ℝ)⁻¹ * Var[Z j; μ] ≤
      Var[fun ω => ∑ i, w i * Z i ω; μ] := by
  classical
  let W : ι → Ω → ℝ := fun i ω => w i * Z i ω
  have hWmem : ∀ i, MemLp (W i) 2 μ := fun i => (hZ i).const_mul (w i)
  have hWpair : Set.Pairwise (↑(Finset.univ : Finset ι) : Set ι)
      (fun i l => W i ⟂ᵢ[μ] W l) := by
    intro i _ l _ hil
    exact IndepFun.comp (hindep hil)
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have hvarsum := ProbabilityTheory.IndepFun.variance_sum
    (μ := μ) (X := W) (s := Finset.univ) (fun i _ => hWmem i) hWpair
  have hweighted :
      Var[fun ω => ∑ i, w i * Z i ω; μ] =
        (∑ i, w i ^ 2) * Var[Z j; μ] := by
    calc
      Var[fun ω => ∑ i, w i * Z i ω; μ] = Var[(∑ i, W i); μ] := by
        congr
        ext ω
        simp [W]
      _ = ∑ i, Var[W i; μ] := hvarsum
      _ = ∑ i, w i ^ 2 * Var[Z i; μ] := by
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [W, ProbabilityTheory.variance_const_mul, pow_two]
      _ = ∑ i, w i ^ 2 * Var[Z j; μ] := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [(hident i).variance_eq]
      _ = (∑ i, w i ^ 2) * Var[Z j; μ] := by
        rw [Finset.sum_mul]
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset ι))
    (f := w) (g := fun _ : ι => (1 : ℝ))
  have hsum_sq_ge : (Fintype.card ι : ℝ)⁻¹ ≤ ∑ i, w i ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hcard_pos]
    convert hcs using 1
    · simp [hw]
    · simp [pow_two, mul_comm]
  have hvar_nonneg : 0 ≤ Var[Z j; μ] :=
    ProbabilityTheory.variance_nonneg (Z j) μ
  calc
    (Fintype.card ι : ℝ)⁻¹ * Var[Z j; μ]
        ≤ (∑ i, w i ^ 2) * Var[Z j; μ] :=
          mul_le_mul_of_nonneg_right hsum_sq_ge hvar_nonneg
    _ = Var[fun ω => ∑ i, w i * Z i ω; μ] := hweighted.symm

/-- **Hansen Theorem 6.11, vector best-linear-unbiased face.**

For scalar weights summing to one, the covariance matrix of the weighted linear
estimator `∑ᵢ wᵢ Zᵢ` dominates the covariance matrix of the equal-weight sample
mean. The proof applies the scalar best-linear-unbiased theorem to every fixed
linear projection and then repackages the result as a positive-semidefinite
matrix inequality. -/
theorem iidLinearUnbiasedEstimator_covMat_sub_sampleMean_posSemidef
    {k : Type*} [Fintype k]
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → k → ℝ} (j : ι) (w : ι → ℝ)
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hindep : Pairwise (fun i l => Z i ⟂ᵢ[μ] Z l))
    (hident : ∀ i, IdentDistrib (Z i) (Z j) μ μ)
    (hw : ∑ i, w i = 1) :
    (covMat μ (fun ω a => ∑ i, w i * Z i ω a) -
      (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j)).PosSemidef := by
  classical
  let Zbar : Ω → k → ℝ := fun ω a => ∑ i, w i * Z i ω a
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian]
    ext a b
    simp [covMat, ProbabilityTheory.covariance_comm]
  · intro a
    have hproj_mem : ∀ i, MemLp (fun ω => Z i ω ⬝ᵥ a) 2 μ :=
      fun i => dotProduct_memLp_two (μ := μ) (hZ i) a
    have hproj_indep : Pairwise (fun i l =>
        (fun ω => Z i ω ⬝ᵥ a) ⟂ᵢ[μ] (fun ω => Z l ω ⬝ᵥ a)) := by
      intro i l hil
      exact IndepFun.comp
        (φ := fun v : k → ℝ => v ⬝ᵥ a)
        (ψ := fun v : k → ℝ => v ⬝ᵥ a)
        (hindep hil) (measurable_dotProduct_right a) (measurable_dotProduct_right a)
    have hproj_ident : ∀ i,
        IdentDistrib (fun ω => Z i ω ⬝ᵥ a) (fun ω => Z j ω ⬝ᵥ a) μ μ := by
      intro i
      simpa [Function.comp_def] using (hident i).comp (measurable_dotProduct_right a)
    have hscalar := iidLinearUnbiasedEstimator_variance_ge_sampleMean
      (μ := μ) (j := j) (w := w) hproj_mem hproj_indep hproj_ident hw
    have hZbar_mem : ∀ b, MemLp (fun ω => Zbar ω b) 2 μ := by
      intro b
      convert (memLp_finset_sum' (s := Finset.univ)
        (f := fun i ω => w i * Z i ω b)
        (fun i _ => ((hZ i).eval b).const_mul (w i))) using 1
      ext ω
      simp [Zbar]
    have hscalar_cov :
        (Fintype.card ι : ℝ)⁻¹ * (a ⬝ᵥ (covMat μ (Z j) *ᵥ a)) ≤
          a ⬝ᵥ (covMat μ Zbar *ᵥ a) := by
      calc
        (Fintype.card ι : ℝ)⁻¹ * (a ⬝ᵥ (covMat μ (Z j) *ᵥ a))
            = (Fintype.card ι : ℝ)⁻¹ * Var[fun ω => Z j ω ⬝ᵥ a; μ] := by
              rw [variance_dotProduct_eq_dotProduct_covMat_mulVec
                (μ := μ) (X := Z j) a (fun b => (hZ j).eval b)]
        _ ≤ Var[fun ω => ∑ i, w i * (Z i ω ⬝ᵥ a); μ] := hscalar
        _ = Var[fun ω => Zbar ω ⬝ᵥ a; μ] := by
              congr
              ext ω
              calc
                ∑ i, w i * (Z i ω ⬝ᵥ a)
                    = ∑ i, ∑ b, w i * (Z i ω b * a b) := by
                      simp [dotProduct, Finset.mul_sum]
                _ = ∑ b, ∑ i, w i * (Z i ω b * a b) := by
                      rw [Finset.sum_comm]
                _ = ∑ b, (∑ i, w i * Z i ω b) * a b := by
                      refine Finset.sum_congr rfl ?_
                      intro b _
                      rw [Finset.sum_mul]
                      simp [mul_assoc]
                _ = Zbar ω ⬝ᵥ a := by
                      simp [Zbar, dotProduct]
        _ = a ⬝ᵥ (covMat μ Zbar *ᵥ a) := by
              rw [variance_dotProduct_eq_dotProduct_covMat_mulVec
                (μ := μ) (X := Zbar) a hZbar_mem]
    have hdiff :
        a ⬝ᵥ ((covMat μ Zbar - (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j)) *ᵥ a) =
          a ⬝ᵥ (covMat μ Zbar *ᵥ a) -
            (Fintype.card ι : ℝ)⁻¹ * (a ⬝ᵥ (covMat μ (Z j) *ᵥ a)) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    change 0 ≤ a ⬝ᵥ ((covMat μ Zbar - (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j)) *ᵥ a)
    rw [hdiff]
    linarith

/-- Variance lower bound from an orthogonal residual decomposition.

This is the scalar Hilbert-space algebra behind best-unbiased-estimator
arguments: if an estimator is the efficient part plus a square-integrable
uncorrelated residual, then its variance dominates the efficient part's variance. -/
theorem variance_le_of_eq_add_uncorrelated
    [IsProbabilityMeasure μ]
    {T M R : Ω → ℝ}
    (hM : MemLp M 2 μ) (hR : MemLp R 2 μ)
    (hT : ∀ ω, T ω = M ω + R ω)
    (hcov : cov[M, R; μ] = 0) :
    Var[M; μ] ≤ Var[T; μ] := by
  have hvarT : Var[T; μ] = Var[M + R; μ] := by
    congr
    ext ω
    exact hT ω
  rw [hvarT, ProbabilityTheory.variance_add hM hR, hcov]
  have hR_nonneg : 0 ≤ Var[R; μ] := ProbabilityTheory.variance_nonneg R μ
  linarith

/-- Vector covariance lower bound from an orthogonal residual decomposition.

This repackages the scalar orthogonal-residual variance inequality along every
fixed linear projection as a positive-semidefinite covariance matrix
inequality. -/
theorem covMat_sub_posSemidef_of_eq_add_uncorrelated
    {k : Type*} [Fintype k]
    [IsProbabilityMeasure μ]
    {T M R : Ω → k → ℝ}
    (hM : MemLp M 2 μ) (hR : MemLp R 2 μ)
    (hT : ∀ ω, T ω = M ω + R ω)
    (hcov : ∀ a : k → ℝ, cov[fun ω => M ω ⬝ᵥ a, fun ω => R ω ⬝ᵥ a; μ] = 0) :
    (covMat μ T - covMat μ M).PosSemidef := by
  classical
  have hTmem : MemLp T 2 μ :=
    (hM.add hR).ae_eq (ae_of_all μ fun ω => (hT ω).symm)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian]
    ext a b
    simp [covMat, ProbabilityTheory.covariance_comm]
  · intro a
    have hscalar := variance_le_of_eq_add_uncorrelated
      (μ := μ)
      (T := fun ω => T ω ⬝ᵥ a)
      (M := fun ω => M ω ⬝ᵥ a)
      (R := fun ω => R ω ⬝ᵥ a)
      (dotProduct_memLp_two (μ := μ) hM a)
      (dotProduct_memLp_two (μ := μ) hR a)
      (fun ω => by
        change T ω ⬝ᵥ a = M ω ⬝ᵥ a + R ω ⬝ᵥ a
        rw [hT ω, add_dotProduct])
      (hcov a)
    have hcov_le :
        a ⬝ᵥ (covMat μ M *ᵥ a) ≤ a ⬝ᵥ (covMat μ T *ᵥ a) := by
      calc
        a ⬝ᵥ (covMat μ M *ᵥ a)
            = Var[fun ω => M ω ⬝ᵥ a; μ] := by
              rw [variance_dotProduct_eq_dotProduct_covMat_mulVec
                (μ := μ) (X := M) a (fun b => hM.eval b)]
        _ ≤ Var[fun ω => T ω ⬝ᵥ a; μ] := hscalar
        _ = a ⬝ᵥ (covMat μ T *ᵥ a) := by
              rw [variance_dotProduct_eq_dotProduct_covMat_mulVec
                (μ := μ) (X := T) a (fun b => hTmem.eval b)]
    have hdiff :
        a ⬝ᵥ ((covMat μ T - covMat μ M) *ᵥ a) =
          a ⬝ᵥ (covMat μ T *ᵥ a) - a ⬝ᵥ (covMat μ M *ᵥ a) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]
    change 0 ≤ a ⬝ᵥ ((covMat μ T - covMat μ M) *ᵥ a)
    rw [hdiff]
    linarith

/-- **Hansen Theorem 6.11, covariance-matrix sample-mean sharpness face.**

For finite-dimensional square-integrable observations whose coordinates are
pairwise independent across distinct observations and whose one-draw covariance
matrix is common across observations, the covariance matrix of the sample mean
is exactly `1 / n` times that one-draw covariance matrix. This is the
matrix-valued version of the sample-mean sharpness identity around Hansen's
best-unbiased-estimation theorem. -/
theorem iidSampleMean_covMat_eq_inv_card_smul
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → k → ℝ} (j : ι)
    (hZ : ∀ i a, MemLp (fun ω => Z i ω a) 2 μ)
    (hindep : ∀ a b, Pairwise (fun i l =>
      (fun ω => Z i ω a) ⟂ᵢ[μ] (fun ω => Z l ω b)))
    (hcov : ∀ i a b,
      cov[fun ω => Z i ω a, fun ω => Z i ω b; μ] =
        cov[fun ω => Z j ω a, fun ω => Z j ω b; μ]) :
    covMat μ (fun ω a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω a) =
      (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j) := by
  classical
  ext a b
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  have hsumcov :
      (∑ i : ι, ∑ l : ι, cov[fun ω => Z i ω a, fun ω => Z l ω b; μ]) =
        (Fintype.card ι : ℝ) *
          cov[fun ω => Z j ω a, fun ω => Z j ω b; μ] := by
    calc
      (∑ i : ι, ∑ l : ι, cov[fun ω => Z i ω a, fun ω => Z l ω b; μ])
          = ∑ i : ι, cov[fun ω => Z i ω a, fun ω => Z i ω b; μ] := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.sum_eq_single i]
            · intro l _ hli
              exact (hindep a b (Ne.symm hli)).covariance_eq_zero (hZ i a) (hZ l b)
            · intro hi
              simp at hi
      _ = ∑ _i : ι, cov[fun ω => Z j ω a, fun ω => Z j ω b; μ] := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hcov i a b
      _ = (Fintype.card ι : ℝ) *
            cov[fun ω => Z j ω a, fun ω => Z j ω b; μ] := by
            simp
  have hsum :
      cov[fun ω => ∑ i : ι, Z i ω a, fun ω => ∑ i : ι, Z i ω b; μ] =
        (Fintype.card ι : ℝ) *
          cov[fun ω => Z j ω a, fun ω => Z j ω b; μ] := by
    rw [ProbabilityTheory.covariance_fun_sum_fun_sum]
    · exact hsumcov
    · intro i
      exact hZ i a
    · intro i
      exact hZ i b
  calc
    covMat μ (fun ω a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω a) a b
        = c ^ 2 *
            cov[fun ω => ∑ i : ι, Z i ω a, fun ω => ∑ i : ι, Z i ω b; μ] := by
          dsimp [covMat, c]
          rw [ProbabilityTheory.covariance_const_mul_left,
            ProbabilityTheory.covariance_const_mul_right]
          ring
    _ = c ^ 2 *
          ((Fintype.card ι : ℝ) *
            cov[fun ω => Z j ω a, fun ω => Z j ω b; μ]) := by
          rw [hsum]
    _ = ((Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j)) a b := by
          have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          dsimp [c, covMat]
          field_simp [hcard]

/-- IID-facing wrapper for `iidSampleMean_covMat_eq_inv_card_smul`.

Vector identical distribution supplies the common one-draw covariance matrix,
while the independence assumption is kept at the coordinate level needed by the
covariance calculation. -/
theorem iidSampleMean_covMat_eq_inv_card_smul_of_identDistrib
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → k → ℝ} (j : ι)
    (hZ : ∀ i a, MemLp (fun ω => Z i ω a) 2 μ)
    (hindep : ∀ a b, Pairwise (fun i l =>
      (fun ω => Z i ω a) ⟂ᵢ[μ] (fun ω => Z l ω b)))
    (hident : ∀ i, IdentDistrib (Z i) (Z j) μ μ) :
    covMat μ (fun ω a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω a) =
      (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j) :=
  iidSampleMean_covMat_eq_inv_card_smul (μ := μ) (j := j) hZ hindep
    (fun i a b => identDistrib_covariance_apply_eq (hident i) a b)

/-- **Hansen Theorem 6.11, scalar orthogonal-residual efficiency face.**

If a square-integrable scalar estimator decomposes into the sample mean plus a
residual that is uncorrelated with the sample mean, then its variance dominates
the sample-mean variance `n⁻¹ Var[Z_j]`. This composes the sharp sample-mean
variance identity with the orthogonal-residual variance algebra; the remaining
arbitrary-estimator task is to derive this orthogonality from a theorem-facing
unbiasedness/completeness condition. -/
theorem iidEstimator_variance_ge_sampleMean_of_mean_add_uncorrelated
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → ℝ} {T R : Ω → ℝ} (j : ι)
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hindep : Pairwise (fun i l => Z i ⟂ᵢ[μ] Z l))
    (hident : ∀ i, IdentDistrib (Z i) (Z j) μ μ)
    (hR : MemLp R 2 μ)
    (hT : ∀ ω, T ω = (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω + R ω)
    (hcov : cov[fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω, R; μ] = 0) :
    (Fintype.card ι : ℝ)⁻¹ * Var[Z j; μ] ≤ Var[T; μ] := by
  classical
  let M : Ω → ℝ := fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω
  have hM : MemLp M 2 μ := by
    convert (memLp_finset_sum' (s := Finset.univ)
      (f := fun i ω => (Fintype.card ι : ℝ)⁻¹ * Z i ω)
      (fun i _ => (hZ i).const_mul (Fintype.card ι : ℝ)⁻¹)) using 1
    ext ω
    simp [M, Finset.mul_sum]
  have hlower := variance_le_of_eq_add_uncorrelated
    (μ := μ) (T := T) (M := M) (R := R) hM hR
    (fun ω => by simpa [M] using hT ω)
    (by simpa [M] using hcov)
  have hsample :
      Var[M; μ] = (Fintype.card ι : ℝ)⁻¹ * Var[Z j; μ] := by
    simpa [M] using
      iidSampleMean_variance_eq_inv_card_mul
        (μ := μ) (j := j) hZ hindep hident
  rwa [← hsample]

/-- **Hansen Theorem 6.11, vector orthogonal-residual efficiency face.**

If a finite-dimensional estimator decomposes into the vector sample mean plus a
square-integrable residual whose every linear projection is uncorrelated with
the corresponding sample-mean projection, then its covariance matrix dominates
`n⁻¹ covMat(Z_j)` in positive-semidefinite order. This is the vector form of the
orthogonal-residual route to Hansen's best-unbiased-estimation bound. -/
theorem iidEstimator_covMat_sub_sampleMean_posSemidef_of_mean_add_uncorrelated
    {k : Type*} [Fintype k]
    [IsProbabilityMeasure μ] [Fintype ι] [Nonempty ι]
    {Z : ι → Ω → k → ℝ} {T R : Ω → k → ℝ} (j : ι)
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hindep : ∀ a b, Pairwise (fun i l =>
      (fun ω => Z i ω a) ⟂ᵢ[μ] (fun ω => Z l ω b)))
    (hident : ∀ i, IdentDistrib (Z i) (Z j) μ μ)
    (hR : MemLp R 2 μ)
    (hT : ∀ ω, T ω =
      (fun a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω a) + R ω)
    (hcov : ∀ a : k → ℝ,
      cov[fun ω => ((fun b => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω b) ⬝ᵥ a),
        fun ω => R ω ⬝ᵥ a; μ] = 0) :
    (covMat μ T - (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j)).PosSemidef := by
  classical
  let M : Ω → k → ℝ := fun ω a => (Fintype.card ι : ℝ)⁻¹ * ∑ i, Z i ω a
  have hM : MemLp M 2 μ := by
    convert (memLp_finset_sum' (s := Finset.univ)
      (f := fun i ω => (Fintype.card ι : ℝ)⁻¹ • Z i ω)
      (fun i _ => (hZ i).const_smul (Fintype.card ι : ℝ)⁻¹)) using 1
    ext ω a
    simp [M, Finset.mul_sum]
  have hpsd := covMat_sub_posSemidef_of_eq_add_uncorrelated
    (μ := μ) (T := T) (M := M) (R := R) hM hR
    (fun ω => by simpa [M] using hT ω)
    (fun a => by simpa [M] using hcov a)
  have hsample :
      covMat μ M = (Fintype.card ι : ℝ)⁻¹ • covMat μ (Z j) := by
    simpa [M] using
      iidSampleMean_covMat_eq_inv_card_smul_of_identDistrib
        (μ := μ) (j := j) (fun i a => (hZ i).eval a) hindep hident
  rwa [hsample] at hpsd

end BestUnbiased

section ArrayCLT

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Even-moment Lyapunov tail bound for scalar triangular arrays.

On the tail event `c ≤ x^2`, the squared summand is bounded by the
`(2 + 2m)`-moment scaled by `c^m`. This is the deterministic scalar inequality
behind an even-moment Lyapunov discharge of Hansen's Lindeberg condition. -/
theorem sq_le_even_moment_div_threshold
    (x c : ℝ) (m : ℕ) (hc : 0 < c) (hcx : c ≤ x ^ 2) :
    x ^ 2 ≤ |x| ^ (2 + 2 * m) / c ^ m := by
  have hx2_nonneg : 0 ≤ |x| ^ 2 := sq_nonneg |x|
  have hcx_abs : c ≤ |x| ^ 2 := by simpa [sq_abs] using hcx
  have hpow : c ^ m ≤ (|x| ^ 2) ^ m := pow_le_pow_left₀ hc.le hcx_abs m
  have hmul : |x| ^ 2 * c ^ m ≤ |x| ^ 2 * (|x| ^ 2) ^ m :=
    mul_le_mul_of_nonneg_left hpow hx2_nonneg
  have hc_pow_pos : 0 < c ^ m := pow_pos hc m
  have hrewrite : |x| ^ 2 * (|x| ^ 2) ^ m = |x| ^ (2 + 2 * m) := by
    rw [← pow_mul]
    rw [← pow_add]
  have hmul' : |x| ^ 2 * c ^ m ≤ |x| ^ (2 + 2 * m) := by
    rw [← hrewrite]
    exact hmul
  have hdiv : |x| ^ 2 ≤ |x| ^ (2 + 2 * m) / c ^ m :=
    (le_div_iff₀ (pow_pos hc m)).2 hmul'
  simpa [sq_abs] using hdiv

/-- Indicator form of `sq_le_even_moment_div_threshold`, matching the
Lindeberg tail summand. -/
theorem sq_tail_indicator_le_even_moment_div_threshold
    (x c : ℝ) (m : ℕ) (hc : 0 < c) :
    Set.indicator {y : ℝ | c ≤ y ^ 2} (fun y => y ^ 2) x ≤
      |x| ^ (2 + 2 * m) / c ^ m := by
  by_cases hx : c ≤ x ^ 2
  · have hxmem : x ∈ {y : ℝ | c ≤ y ^ 2} := hx
    rw [Set.indicator_of_mem hxmem]
    exact sq_le_even_moment_div_threshold x c m hc hx
  · have hxnot : x ∉ {y : ℝ | c ≤ y ^ 2} := hx
    rw [Set.indicator_of_notMem hxnot]
    exact div_nonneg (pow_nonneg (abs_nonneg x) _) (pow_nonneg hc.le m)

/-- Expected-tail form of the even-moment Lyapunov bound. This is the scalar
estimate used to turn a higher even moment into a Lindeberg tail bound once the
array normalization supplies the threshold `c`. -/
theorem integral_sq_tail_le_integral_even_moment_div_threshold
    (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) (m : ℕ) (hc : 0 < c)
    (h_tail : Integrable
      (fun ω => Set.indicator {y : ℝ | c ≤ y ^ 2} (fun y => y ^ 2) (X ω)) μ)
    (h_moment : Integrable (fun ω => |X ω| ^ (2 + 2 * m)) μ) :
    ∫ ω, Set.indicator {y : ℝ | c ≤ y ^ 2} (fun y => y ^ 2) (X ω) ∂μ ≤
      (∫ ω, |X ω| ^ (2 + 2 * m) ∂μ) / c ^ m := by
  have h_rhs_int : Integrable (fun ω => |X ω| ^ (2 + 2 * m) / c ^ m) μ :=
    h_moment.div_const (c ^ m)
  have hmono :
      (fun ω => Set.indicator {y : ℝ | c ≤ y ^ 2} (fun y => y ^ 2) (X ω)) ≤
        fun ω => |X ω| ^ (2 + 2 * m) / c ^ m := by
    intro ω
    exact sq_tail_indicator_le_even_moment_div_threshold (X ω) c m hc
  have hle := MeasureTheory.integral_mono h_tail h_rhs_int hmono
  simpa [MeasureTheory.integral_div] using hle

/-- Finite-row version of the expected Lyapunov tail bound, matching the
finite sums in triangular-array Lindeberg conditions. -/
theorem sum_integral_sq_tail_le_sum_integral_even_moment_div_threshold
    {ι : Type*} [Fintype ι]
    (μ : Measure Ω) (X : ι → Ω → ℝ) (c : ℝ) (m : ℕ) (hc : 0 < c)
    (h_tail : ∀ i, Integrable
      (fun ω => Set.indicator {y : ℝ | c ≤ y ^ 2} (fun y => y ^ 2) (X i ω)) μ)
    (h_moment : ∀ i, Integrable (fun ω => |X i ω| ^ (2 + 2 * m)) μ) :
    (∑ i, ∫ ω, Set.indicator {y : ℝ | c ≤ y ^ 2} (fun y => y ^ 2) (X i ω) ∂μ) ≤
      ∑ i, (∫ ω, |X i ω| ^ (2 + 2 * m) ∂μ) / c ^ m := by
  exact Finset.sum_le_sum fun i _ =>
    integral_sq_tail_le_integral_even_moment_div_threshold μ (X i) c m hc
      (h_tail i) (h_moment i)

/-- Normalized finite-row Lyapunov tail bound. This is the direct algebraic
shape of the scalar Lindeberg expression once the normalization is fixed. -/
theorem normalized_sum_integral_sq_tail_le_normalized_even_moment_bound
    {ι : Type*} [Fintype ι]
    (μ : Measure Ω) (X : ι → Ω → ℝ) (c scale : ℝ) (m : ℕ)
    (hc : 0 < c) (hscale : 0 ≤ scale)
    (h_tail : ∀ i, Integrable
      (fun ω => Set.indicator {y : ℝ | c ≤ y ^ 2} (fun y => y ^ 2) (X i ω)) μ)
    (h_moment : ∀ i, Integrable (fun ω => |X i ω| ^ (2 + 2 * m)) μ) :
    scale * (∑ i,
      ∫ ω, Set.indicator {y : ℝ | c ≤ y ^ 2} (fun y => y ^ 2) (X i ω) ∂μ) ≤
        scale * ∑ i, (∫ ω, |X i ω| ^ (2 + 2 * m) ∂μ) / c ^ m := by
  exact mul_le_mul_of_nonneg_left
    (sum_integral_sq_tail_le_sum_integral_even_moment_div_threshold
      μ X c m hc h_tail h_moment)
    hscale

/-- Projection-level sufficient condition package for Hansen's multivariate
Lindeberg CLT.

The scalar Lindeberg proof obligations are represented by the projection CLT
field. This package keeps the chapter-facing multivariate endpoint usable while
leaving the scalar triangular-array Lindeberg theorem as the remaining
probability-engine task. -/
structure MultivariateLindebergCLTConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ → Ω → (k → ℝ)) (S : Matrix k k ℝ) where
  /-- A.e. measurability of the normalized array statistic at each sample size. -/
  aemeasurable : ∀ n, AEMeasurable (T n) μ
  /-- Scalar projection CLTs against the matching multivariate Gaussian law. -/
  projection_clt : ∀ a : k → ℝ,
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ a)
      atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
      (fun _ => μ)
      (multivariateGaussian 0 S)

/-- **Hansen Theorem 6.4, multivariate Lindeberg CLT endpoint.**

Once scalar projection Lindeberg CLTs are available for a normalized triangular
array statistic, Cramér-Wold gives the corresponding multivariate Gaussian
limit. The textbook normalization `V_n^{-1/2} ∑ᵢ Y_{ni}` is represented by the
user-supplied statistic `T`. -/
theorem multivariateLindebergCLT_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → (k → ℝ)} {S : Matrix k k ℝ}
    (h : MultivariateLindebergCLTConditions μ T S) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (T n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 S) :=
  vectorCLT_tendstoInDistribution_multivariateGaussian_of_projections
    h.aemeasurable h.projection_clt

/-- Indexed projection-level sufficient condition package for Hansen's
multivariate Lindeberg CLT.

This is the indexed-source-space analogue of
`MultivariateLindebergCLTConditions`, intended for triangular-array or bootstrap
CLTs whose row probability space varies with the sample size. -/
structure MultivariateIndexedLindebergCLTConditions
    (Ωrow : ℕ → Type*) [∀ n, MeasurableSpace (Ωrow n)]
    (P : ∀ n, Measure (Ωrow n)) [∀ n, IsProbabilityMeasure (P n)]
    (T : ∀ n, Ωrow n → (k → ℝ)) (S : Matrix k k ℝ) where
  /-- A.e. measurability of the normalized indexed-array statistic in each row. -/
  aemeasurable : ∀ n, AEMeasurable (T n) (P n)
  /-- Scalar projection CLTs against the matching multivariate Gaussian law. -/
  projection_clt : ∀ a : k → ℝ,
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ a)
      atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
      P
      (multivariateGaussian 0 S)

/-- Indexed multivariate Lindeberg CLT endpoint.

Once scalar projection Lindeberg CLTs are available for an indexed normalized
array statistic, indexed Cramér-Wold gives the corresponding multivariate
Gaussian limit. This is the source-space-varying analogue of
`multivariateLindebergCLT_tendstoInDistribution`. -/
theorem multivariateIndexedLindebergCLT_tendstoInDistribution
    {Ωrow : ℕ → Type*} [∀ n, MeasurableSpace (Ωrow n)]
    {P : ∀ n, Measure (Ωrow n)} [∀ n, IsProbabilityMeasure (P n)]
    {T : ∀ n, Ωrow n → (k → ℝ)} {S : Matrix k k ℝ}
    (h : MultivariateIndexedLindebergCLTConditions Ωrow P T S) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (T n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      P
      (multivariateGaussian 0 S) :=
  vectorCLT_tendstoInDistribution_multivariateGaussian_of_projections_indexed
    h.aemeasurable h.projection_clt

/-- Projection-level sufficient condition package for Hansen's heterogeneous
array CLT. The statistic `T n` is typically `√n * \bar Y_n`; the limit
covariance is the supplied matrix `V`. -/
abbrev HeterogeneousArrayCLTConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ → Ω → (k → ℝ)) (V : Matrix k k ℝ) :=
  MultivariateLindebergCLTConditions μ T V

/-- **Hansen Theorem 6.5, heterogeneous-array CLT endpoint.**

This is the multivariate Cramér-Wold assembly for the heterogeneous-array CLT:
scalar projection CLTs for the normalized sample average imply convergence to
the centered Gaussian with covariance `V`. -/
theorem heterogeneousArrayCLT_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : ℕ → Ω → (k → ℝ)} {V : Matrix k k ℝ}
    (h : HeterogeneousArrayCLTConditions μ T V) :
    TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (T n ω))
      atTop
      (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ)
      (multivariateGaussian 0 V) :=
  multivariateLindebergCLT_tendstoInDistribution h

end ArrayCLT

end HansenEconometrics
