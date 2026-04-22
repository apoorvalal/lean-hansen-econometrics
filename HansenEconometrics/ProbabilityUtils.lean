import Mathlib

open MeasureTheory ProbabilityTheory
open Matrix
open scoped ENNReal Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Sum of squares of a finite family of real-valued random variables. This is the basic random
variable behind chi-square style constructions. -/
def sumSquaresRV [Fintype ι] (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, (X i ω) ^ 2

lemma sumSquaresRV_nonneg [Fintype ι] (X : ι → Ω → ℝ) (ω : Ω) :
    0 ≤ sumSquaresRV X ω := by
  unfold sumSquaresRV
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Convenient wrapper around Mathlib's jointly-Gaussian + zero-covariance independence lemma for
real-valued pairs. -/
lemma indep_of_jointGaussian_cov_zero
    {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hcov : cov[X, Y; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_eq_zero hcov

/-- Finite-family version of Gaussian independence from pairwise zero covariance. -/
lemma iIndep_of_jointGaussian_cov_zero [Finite ι]
    {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω i => X i ω) P)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_eq_zero hcov

section MultivariateGaussian

variable {n : Type*}
variable [Fintype n] [DecidableEq n]

/-- In an isotropic multivariate Gaussian, the coordinates in any orthonormal basis, scaled by the
standard deviation, are independent standard normals. This is the bridge from Gaussian vectors to
chi-square arguments in Chapter 5. -/
theorem orthonormalBasis_coords_div_sqrt_iIndep_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    {σ2 : ℝ} (hσ2 : 0 < σ2) (e : Ω → EuclideanSpace ℝ n)
    (he : HasLaw e (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    let W : n → Ω → ℝ := fun i ω => (b.repr (e ω)).ofLp i / Real.sqrt σ2
    (∀ i, HasLaw (W i) (gaussianReal 0 1) μ) ∧ ProbabilityTheory.iIndepFun W μ := by
  let Z : n → Ω → ℝ := fun i ω => (b.repr (e ω)).ofLp i
  let S : Matrix n n ℝ := (σ2 : ℝ) • (1 : Matrix n n ℝ)
  have hS : S.PosSemidef := by
    simpa [S, smul_one_eq_diagonal] using
      (Matrix.PosSemidef.diagonal (n := n) (d := fun _ => σ2) fun _ => hσ2.le)
  have hZ_gauss : HasGaussianLaw (fun ω => b.repr (e ω)) μ := by
    let L : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [L] using (he.hasGaussianLaw.map_fun L)
  have hmeanZ : ∀ i, μ[Z i] = 0 := by
    intro i
    let Li : EuclideanSpace ℝ n →L[ℝ] ℝ :=
      (EuclideanSpace.proj i).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap
    rw [show (fun ω => Z i ω) = Li ∘ e by
      funext ω
      simp [Z, Li]]
    rw [he.integral_comp (Measurable.aestronglyMeasurable <| by fun_prop)]
    rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp [integral_id_multivariateGaussian]
    · exact IsGaussian.integrable_id (μ := multivariateGaussian 0 S)
  have hcovZ : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0 := by
    intro i j
    have hZi : (fun x : EuclideanSpace ℝ n => (b.repr x).ofLp i) =
        fun x => inner ℝ (b i) x := by
      funext x
      simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := i))
    have hZj : (fun x : EuclideanSpace ℝ n => (b.repr x).ofLp j) =
        fun x => inner ℝ (b j) x := by
      funext x
      simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := j))
    rw [he.covariance_fun_comp (f := fun x : EuclideanSpace ℝ n => (b.repr x).ofLp i)
      (g := fun x : EuclideanSpace ℝ n => (b.repr x).ofLp j) (by fun_prop) (by fun_prop), hZi, hZj,
      ← covarianceBilin_apply_eq_cov]
    · rw [covarianceBilin_multivariateGaussian hS]
      by_cases hij : i = j
      · subst hij
        rw [smul_mulVec, one_mulVec, dotProduct_smul]
        have hdot : (b i).ofLp ⬝ᵥ (b i).ofLp = 1 := by
          calc
            (b i).ofLp ⬝ᵥ (b i).ofLp = ‖b i‖ ^ 2 := by
              simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq (b i)).symm
            _ = 1 := by nlinarith [b.norm_eq_one i]
        simp [hdot]
      · rw [smul_mulVec, one_mulVec, dotProduct_smul]
        have hdot : (b i).ofLp ⬝ᵥ (b j).ofLp = 0 := by
          have hInner : inner ℝ (b i) (b j) = 0 := by
            simpa [hij] using (orthonormal_iff_ite.mp b.orthonormal i j)
          have htoInner' : inner ℝ (b j) (b i) = (b i).ofLp ⬝ᵥ (b j).ofLp := by
            rw [PiLp.inner_apply, dotProduct]
            refine Finset.sum_congr rfl ?_
            intro a ha
            have hscalar : inner ℝ ((b j).ofLp a) ((b i).ofLp a) =
                (b j).ofLp a * (b i).ofLp a := by
              simpa using (RCLike.inner_apply' ((b j).ofLp a) ((b i).ofLp a))
            simpa [mul_comm] using hscalar
          calc
            (b i).ofLp ⬝ᵥ (b j).ofLp = inner ℝ (b j) (b i) := by
              exact htoInner'.symm
            _ = inner ℝ (b i) (b j) := by rw [real_inner_comm]
            _ = 0 := hInner
        simp [hij, hdot]
    · exact IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)
  have hZ_gauss_family : HasGaussianLaw (fun ω ↦ (Z · ω)) μ := by
    simpa [Z] using
      hZ_gauss.map_equiv (EuclideanSpace.equiv n ℝ)
  have hZ_indep : ProbabilityTheory.iIndepFun Z μ :=
    hZ_gauss_family.iIndepFun_of_covariance_eq_zero fun i j hij => by
      rw [hcovZ i j, if_neg hij]
  have hW_law : ∀ i, HasLaw (fun ω => Z i ω / Real.sqrt σ2) (gaussianReal 0 1) μ := by
    intro i
    have hZi_law : HasLaw (Z i) (gaussianReal 0 ⟨σ2, hσ2.le⟩) μ := by
      let Li : EuclideanSpace ℝ n →L[ℝ] ℝ :=
        (EuclideanSpace.proj i).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap
      have hLiMap : (multivariateGaussian 0 S).map Li = gaussianReal 0 ⟨σ2, hσ2.le⟩ := by
        have hEq := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) Li
        have hMean : (multivariateGaussian 0 S)[Li] = 0 := by
          rw [ContinuousLinearMap.integral_comp_id_comm]
          · simp [integral_id_multivariateGaussian]
          · exact IsGaussian.integrable_id (μ := multivariateGaussian 0 S)
        have hVar : Var[Li; multivariateGaussian 0 S] = σ2 := by
          rw [← covariance_self (Measurable.aemeasurable <| by fun_prop), show Li = fun x => inner ℝ (b i) x by
            ext x
            simpa [Li] using (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := i))
            , ← covarianceBilin_apply_eq_cov]
          · rw [covarianceBilin_multivariateGaussian hS, smul_mulVec, one_mulVec, dotProduct_smul]
            have hdot : (b i).ofLp ⬝ᵥ (b i).ofLp = 1 := by
              calc
                (b i).ofLp ⬝ᵥ (b i).ofLp = ‖b i‖ ^ 2 := by
                  simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq (b i)).symm
                _ = 1 := by nlinarith [b.norm_eq_one i]
            simp [hdot]
          · exact IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)
        rw [hMean, hVar, Real.toNNReal_of_nonneg hσ2.le] at hEq
        simpa using hEq
      refine (HasLaw.comp ⟨by fun_prop, hLiMap⟩ he).congr ?_
      filter_upwards with ω
      simp [Z, Li]
    convert gaussianReal_div_const hZi_law (Real.sqrt σ2) using 2
    · simp
    · ext
      simp [Real.sq_sqrt hσ2.le, hσ2.ne']
  have hW_indep : ProbabilityTheory.iIndepFun (fun i ω => Z i ω / Real.sqrt σ2) μ := by
    exact hZ_indep.comp (fun _ x => x / Real.sqrt σ2) fun _ => measurable_id.div_const _
  change (∀ i, HasLaw (fun ω => Z i ω / Real.sqrt σ2) (gaussianReal 0 1) μ) ∧
      ProbabilityTheory.iIndepFun (fun i ω => Z i ω / Real.sqrt σ2) μ
  exact And.intro hW_law hW_indep

end MultivariateGaussian

end HansenEconometrics
