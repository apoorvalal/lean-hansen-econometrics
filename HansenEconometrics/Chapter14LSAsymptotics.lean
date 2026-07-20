import Mathlib.LinearAlgebra.Matrix.PosDef
import HansenEconometrics.Chapter14WoldL2
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.ErgodicTheory.MeanErgodic
import HansenEconometrics.Chapter14CLT
import HansenEconometrics.Chapter14Mixing
import HansenEconometrics.Chapter7Asymptotics.SandwichAssembly
import HansenEconometrics.AsymptoticUtils.StochasticOrder

/-!
# Chapter 14: Least-squares asymptotics (Theorems 14.27–14.35)

Identification, consistency, asymptotic normality, and covariance-matrix estimation.

This file develops the least-squares-asymptotics layer of Chapter 14. It lands the identification
foundation (Theorems 14.27–14.28), least-squares consistency (Theorem 14.29 for an AR(p), Theorem
14.35(a) for a general time-series regression), and asymptotic normality of the AR(p) least-squares
estimator (Theorem 14.30, and its conditionally homoskedastic specialization Theorem 14.31),
conditional on the vector martingale-difference central limit theorem (Theorem 14.11, supplied as
the bundle `MDSCLTConditionsVec`). It further lands asymptotic normality under general dependence:
Theorem **14.32** (AR(p) normality for a strictly stationary α-mixing process whose fit is the best
linear predictor) and Theorem **14.35(b)(c)** (time-series regression normality in the
martingale-difference and α-mixing cases). It closes the layer with **14.33** (covariance-matrix
estimation for the AR(p) least-squares estimator): the estimator-consistency core — residual
variance `σ̂² →ₚ 𝔼[e₀²]` and homoskedastic sandwich `V̂⁰ = σ̂² Q̂⁻¹ →ₚ σ² Q⁻¹` — is fully proved,
while the studentized t-ratio (14.33(b)) and Newey–West/HAC estimator (**14.34**) are documented
deferrals. A campaign note flags Hansen's textual slip on 14.33 ("under the assumptions of Theorem
14.32" should read Theorem 14.30, the correctly-specified estimator); see the §14.33/14.34 section
docstring.

## Asymptotic normality under general dependence (Theorem 14.32 and 14.35(b)(c))

`ProbabilityTheory.summable_autocov_scoreProj_of_mixing` is the **unconditional** core of Theorem
14.32: under `ARMixingConditions` (`Lʳ`, `r > 4`, `∑ α(ℓ)^{1−4/r} < ∞`) every linear projection of
the score `wₜ = eₜ xₜ` has absolutely summable autocovariances, so its long-run variance is well
defined (the score is a `(p+1)`-lag transformation of `Y`, so Hansen Theorem 14.12 dominates its
mixing coefficients and the Davydov bound of `summable_autocov_of_mixing` supplies summability).
The normality endpoints `ProbabilityTheory.arLS_asymptoticNormal_mixing` (14.32),
`ProbabilityTheory.tsRegression_asymptoticNormal` (14.35(b)), and
`ProbabilityTheory.tsRegression_asymptoticNormal_mixing` (14.35(c)) are bundle-conditional on the
relevant vector central limit theorem — `ProbabilityTheory.MixingCLTConditionsVec` (the α-mixing
vector CLT, Hansen 14.15, whose `central_limit` mirrors `MDSCLTConditionsVec.central_limit`) or
`MDSCLTConditionsVec` — with the long-run covariance matrix carried as an explicit field tied to the
projected long-run variances (`variance_proj`). All three share the Slutsky assembly engine
`leastSquares_asymptoticNormal_of_scoreCLT`, fed by the boundary-correction engine
`sampleSum_unshift_tendstoInDistribution` and the score tightness engine
`boundedInProbabilityNorm_shiftEquivariant`.

## Asymptotic normality (Theorems 14.30 and 14.31)

`ProbabilityTheory.arLS_asymptoticNormal` is Hansen **Theorem 14.30**: under correct specification
with a martingale-difference innovation (`ARModelConditions`), conditional on the score central
limit theorem bundle and strict stationarity of `Y`, `√n(α̂ₙ − α) ⇒ Q⁻¹ Z` with `Z` carrying the
Gaussian score law `multivariateGaussian 0 Σ` (`Σ` the score covariance, `Q = arGram Y P p`). The
proof is the Chapter 7 Slutsky chain: the score CLT (`sampleScore_tendstoInDistribution`, whose
boundary term against the bundle's `t+1` indexing is discharged using the score's `Oₚ(1)` bound,
itself derived from strict stationarity in `score_boundedInProbabilityNorm`), the random-inverse
composition `matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix`, and the singular-event
residual `arLS_residual_tendstoInMeasure_zero`. `ProbabilityTheory.arProjCoeff_eq_coeff` identifies
`α = arProjCoeff Y P p = coeff` from the normal equations and the MDS orthogonality `𝔼[x₀ e₀] = 0`.
`ProbabilityTheory.arLS_asymptoticNormal_homoskedastic` is Hansen **Theorem 14.31**: under
conditional homoskedasticity `𝔼[eₜ² | ℱₜ₋₁] = σ²` and strict stationarity the score covariance
collapses to `Σ = σ² Q` (`covMat_eq_smul_arGram`), giving the sandwich covariance `σ² Q⁻¹`.

## The AR design and its second-moment (Gram) matrix

For a real process `X : ℤ → Ω → ℝ` the regressor vector of an autoregression of order `p` is the
`(p+1)`-vector `(1, X_{t−1}, …, X_{t−p})` (index `0` is the intercept). Two definitions carry this:

* `ProbabilityTheory.arDesign X p t ω : Fin (p+1) → ℝ` — the design vector at time `t`.
* `ProbabilityTheory.arGram X P p : Matrix (Fin (p+1)) (Fin (p+1)) ℝ` — its (uncentered)
  second-moment matrix `Q = E[design · designᵀ]`, anchored at `t = 0`. The intercept makes this the
  raw second moment rather than a covariance, which is exactly what identification needs.

The quadratic form of `arGram` is the mean square of the linear form
(`ProbabilityTheory.dotProduct_arGram_mulVec`): `a ⬝ᵥ (Q *ᵥ a) = E[(a ⬝ᵥ design)²] ≥ 0`.

## Identification (Theorems 14.28 and 14.27)

`ProbabilityTheory.arGram_posDef` is Hansen **Theorem 14.28** — the primary statement, since the
proof never uses that the AR model is correctly specified. For a strictly stationary,
square-integrable process that is *not purely deterministic* (positive one-step prediction-error
variance `σ² > 0`, in the path-space form supplied by `Chapter14WoldL2`), the design second-moment
matrix is positive definite. The mechanism: if `a ⬝ᵥ (Q *ᵥ a) = 0` for `a ≠ 0` then
`a ⬝ᵥ design = 0` almost surely, an exact linear relation among `{1, X_{t−1}, …, X_{t−p}}`; solving
for the most recent involved lag exhibits that coordinate as an element of its own strict past, so
the corresponding Wold prediction error vanishes, and by stationarity of the error variance `σ² = 0`
— contradiction. The almost-sure relation is transported to the path law (`ae_map_iff`) so the
path-space stationarity lemma `norm_woldError_pathCoord_eq` applies.

`ProbabilityTheory.arGram_posDef_of_ar` is Hansen **Theorem 14.27**, the correctly-specified AR(p)
instance (the AR hypothesis adds nothing to the Gram argument), together with the canonical
projection coefficient vector `ProbabilityTheory.arProjCoeff` `= Q⁻¹ E[design · X_t]` and its normal
equation `ProbabilityTheory.arGram_mulVec_arProjCoeff`. These are the objects the LS-consistency
theorem (14.29) consumes.

## Least-squares consistency (Theorems 14.29 and 14.35(a))

`ProbabilityTheory.arLS_consistent` is Hansen **Theorem 14.29**: the least-squares AR(p) coefficient
`ProbabilityTheory.arLSStar` `= Q̂ₙ⁻¹ ĉₙ` converges in probability to the projection coefficient
`arProjCoeff`. `ProbabilityTheory.tsRegression_consistent` is **Theorem 14.35(a)**, the same
conclusion for a general time-series regression bundled by
`ProbabilityTheory.TSRegressionConditions`. Both are instances of one shared engine,
`tendstoInMeasure_ergodicAverage_pathFunctional`: for an ergodic base process and a measurable path
functional, the sample average along shifted paths converges to the mean, packaging
`IsErgodicProcess.comp_shiftEquivariant` (14.5) with the ergodic theorem in probability
(`IsErgodicProcess.tendstoInMeasure_average`, 14.9(b)). Each sample-Gram/cross-moment entry is such
an average; the matrix continuous-mapping lemmas of `AsymptoticUtils`
(`tendstoInMeasure_matrix_inv`, `tendstoInMeasure_mulVec`) then compose the entrywise limits, with
positive definiteness of `Q` (14.28) supplying the invertibility of the limit. Variance estimation
(`σ̂²`) and the normality parts 14.35(b)(c) are deferred to later work packages (14.33 handles
covariance-matrix estimation).
-/

open MeasureTheory Filter Topology Matrix

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The AR(p) design vector** at time `t`: `(1, X_{t−1}, …, X_{t−p})` as a map
`Fin (p+1) → ℝ`. Index `0` is the intercept; index `i ≥ 1` is the lag `X_{t−i}`. -/
noncomputable def arDesign (X : ℤ → Ω → ℝ) (p : ℕ) (t : ℤ) (ω : Ω) : Fin (p + 1) → ℝ :=
  fun i => if i = 0 then 1 else X (t - (i.val : ℤ)) ω

/-- **The AR(p) Gram matrix** — the (uncentered) second-moment matrix of the design vector, anchored
at `t = 0`: `Q_{ij} = E[design_i · design_j]`. The intercept coordinate makes this the raw second
moment `E[x_t x_tᵀ]`, Hansen's `Q`. -/
noncomputable def arGram (X : ℤ → Ω → ℝ) (P : Measure Ω) (p : ℕ) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  fun i j => ∫ ω, arDesign X p 0 ω i * arDesign X p 0 ω j ∂P

variable {X : ℤ → Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P]

/-- Each design coordinate is square integrable: the intercept is a constant and the lags inherit
`MemLp` from the process. -/
theorem memLp_arDesign (hL2 : ∀ s, MemLp (X s) 2 P) (p : ℕ) (i : Fin (p + 1)) :
    MemLp (fun ω => arDesign X p 0 ω i) 2 P := by
  by_cases h : i = 0
  · simp only [arDesign, if_pos h]
    exact memLp_const 1
  · simp only [arDesign, if_neg h]
    exact hL2 _

/-- **The quadratic form of the Gram matrix is a mean square.** `a ⬝ᵥ (Q *ᵥ a) = E[(a ⬝ᵥ design)²]`.
This is the identity behind both positive semidefiniteness and the definiteness argument. -/
theorem dotProduct_arGram_mulVec (hL2 : ∀ s, MemLp (X s) 2 P) (p : ℕ) (a : Fin (p + 1) → ℝ) :
    a ⬝ᵥ (arGram X P p *ᵥ a) = ∫ ω, (a ⬝ᵥ arDesign X p 0 ω) ^ 2 ∂P := by
  have hInt : ∀ i j, Integrable (fun ω => arDesign X p 0 ω i * arDesign X p 0 ω j) P :=
    fun i j => (memLp_arDesign hL2 p i).integrable_mul (memLp_arDesign hL2 p j)
  have hInt2 : ∀ i j, Integrable
      (fun ω => a i * arDesign X p 0 ω i * (a j * arDesign X p 0 ω j)) P := by
    intro i j
    refine ((hInt i j).const_mul (a i * a j)).congr ?_
    filter_upwards with ω; ring
  have step1 : a ⬝ᵥ (arGram X P p *ᵥ a)
      = ∑ i, ∑ j, ∫ ω, a i * arDesign X p 0 ω i * (a j * arDesign X p 0 ω j) ∂P := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [arGram, show a i * ((∫ ω, arDesign X p 0 ω i * arDesign X p 0 ω j ∂P) * a j)
        = (a i * a j) * ∫ ω, arDesign X p 0 ω i * arDesign X p 0 ω j ∂P from by ring,
      ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have step2 : (∑ i, ∑ j, ∫ ω, a i * arDesign X p 0 ω i * (a j * arDesign X p 0 ω j) ∂P)
      = ∫ ω, ∑ i, ∑ j, a i * arDesign X p 0 ω i * (a j * arDesign X p 0 ω j) ∂P := by
    have inner : ∀ i, (∑ j, ∫ ω, a i * arDesign X p 0 ω i * (a j * arDesign X p 0 ω j) ∂P)
        = ∫ ω, ∑ j, a i * arDesign X p 0 ω i * (a j * arDesign X p 0 ω j) ∂P :=
      fun i => (integral_finset_sum _ fun j _ => hInt2 i j).symm
    simp_rw [inner]
    rw [← integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hInt2 i j)]
  rw [step1, step2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [← Finset.sum_mul_sum]
  simp only [dotProduct]
  ring

omit [IsFiniteMeasure P] in
/-- The Gram matrix is symmetric, hence Hermitian over `ℝ`. -/
theorem arGram_isHermitian (p : ℕ) :
    (arGram X P p).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, star_trivial, arGram, arGram]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

/-- The coercion of a finite `Lp`-sum to a function is a.e. the pointwise sum of coercions. -/
private theorem coeFn_lpSum {ι : Type*} [DecidableEq ι] {μ : Measure Ω} (s : Finset ι)
    (f : ι → Lp ℝ 2 μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] ∑ i ∈ s, ⇑(f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℝ 2 μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    simp only [Pi.add_apply, h1, h2]

/-- The constant-one element of `Lp` over a probability measure is nonzero. -/
private theorem oneLp_ne_zero {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω')
    [IsProbabilityMeasure μ] : oneLp μ ≠ 0 := by
  intro h
  have hc : ⇑(oneLp μ) =ᵐ[μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _
  rw [h] at hc
  have hz : (fun _ : Ω' => (1 : ℝ)) =ᵐ[μ] (0 : Ω' → ℝ) := hc.symm.trans (Lp.coeFn_zero ℝ 2 μ)
  have hfalse : ∀ᵐ _x ∂μ, (1 : ℝ) = 0 := by
    filter_upwards [hz] with x hx; simp at hx
  exact one_ne_zero (Filter.eventually_const.mp hfalse)

/-- **The contradiction engine for Theorem 14.28.** If a nonzero coefficient vector annihilates the
design almost surely, the one-step prediction-error variance vanishes. The almost-sure relation is a
nontrivial exact linear dependence among `{1, X_{−1}, …, X_{−p}}`; transported to the path law it
places the most recent involved coordinate in its own strict past, so the Wold error there is zero,
and path-space stationarity of the error norm carries this to time `0`. -/
private theorem projErrorVariance_eq_zero_of_ae_dotProduct [IsProbabilityMeasure P]
    (hSS : IsStrictlyStationary X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hL2 : ∀ s, MemLp (X s) 2 P)
    {p : ℕ} {a : Fin (p + 1) → ℝ} (ha : a ≠ 0)
    (hrel : ∀ᵐ ω ∂P, a ⬝ᵥ arDesign X p 0 ω = 0) :
    projErrorVariance pathCoord (pathLaw X P) (memLp_pathCoord_pathLaw hmeas hL2) = 0 := by
  classical
  set hE := memLp_pathCoord_pathLaw hmeas hL2 with hE_def
  set μ := pathLaw X P with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_pathLaw hmeas
  -- coordinate measurability of the path-space design
  have hcoord : ∀ i : Fin (p + 1), Measurable (fun x : ℤ → ℝ => arDesign pathCoord p 0 x i) := by
    intro i
    by_cases h : i = 0
    · simp only [arDesign, if_pos h]; exact measurable_const
    · simp only [arDesign, if_neg h]; exact measurable_pathCoord _
  have hSmeas : MeasurableSet {x : ℤ → ℝ | a ⬝ᵥ arDesign pathCoord p 0 x = 0} := by
    have hmeasf : Measurable (fun x : ℤ → ℝ => a ⬝ᵥ arDesign pathCoord p 0 x) := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun i _ => (hcoord i).const_mul (a i)
    exact hmeasf (measurableSet_singleton 0)
  -- Step A: transport the a.e. relation to the path law.
  have hrel_path : ∀ᵐ x ∂μ, a ⬝ᵥ arDesign pathCoord p 0 x = 0 := by
    rw [hμ, pathLaw, ae_map_iff (aemeasurable_pi_iff.mpr hmeas) hSmeas]
    filter_upwards [hrel] with ω hω
    exact hω
  -- Step B: the design as `Lp` elements and the exact relation `L = 0`.
  set d : Fin (p + 1) → Lp ℝ 2 μ :=
    fun i => if i = 0 then oneLp μ else (hE (0 - (i.val : ℤ))).toLp with hd_def
  have hd0 : d 0 = oneLp μ := by rw [hd_def]; simp
  have hdi : ∀ i, i ≠ 0 → d i = (hE (0 - (i.val : ℤ))).toLp := by
    intro i hi; rw [hd_def]; simp [hi]
  have hone_coe : ⇑(oneLp μ) =ᵐ[μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _
  have hd_coe : ∀ i, ⇑(d i) =ᵐ[μ] fun x => arDesign pathCoord p 0 x i := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      rw [hd0]
      filter_upwards [hone_coe] with x hx
      rw [hx]; simp [arDesign]
    · rw [hdi i hi0]
      filter_upwards [MemLp.coeFn_toLp (hE (0 - (i.val : ℤ)))] with x hx
      rw [hx]; simp only [arDesign, if_neg hi0]
  have hL_coe : ⇑(∑ i, a i • d i) =ᵐ[μ] fun x => a ⬝ᵥ arDesign pathCoord p 0 x := by
    have hsmul : ∀ i, ⇑(a i • d i) =ᵐ[μ] a i • ⇑(d i) := fun i => Lp.coeFn_smul (a i) (d i)
    filter_upwards [coeFn_lpSum Finset.univ fun i => a i • d i, ae_all_iff.mpr hsmul,
      ae_all_iff.mpr hd_coe] with x hsum hs hdc
    rw [hsum, Finset.sum_apply, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs i, Pi.smul_apply, smul_eq_mul, hdc i]
  have hL0 : (∑ i, a i • d i) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hL_coe, hrel_path] with x hc hr
    simp only [Pi.zero_apply]; rw [hc]; exact hr
  -- Step C: the most recent active lag lies in its own strict past.
  set A : Finset (Fin (p + 1)) := Finset.univ.filter (fun k => 1 ≤ k.val ∧ a k ≠ 0) with hA_def
  have hmem_A : ∀ k : Fin (p + 1), k ∈ A ↔ (1 ≤ k.val ∧ a k ≠ 0) := by
    intro k; rw [hA_def, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  have hlag_ne : ∀ k : Fin (p + 1), k ≠ 0 → 1 ≤ k.val := by
    intro k hk
    have : k.val ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
    omega
  have hA_ne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hAe
    apply ha
    have hzero_lag : ∀ k : Fin (p + 1), k ≠ 0 → a k = 0 := by
      intro k hk
      by_contra hak
      have hkA : k ∈ A := (hmem_A k).mpr ⟨hlag_ne k hk, hak⟩
      rw [hAe] at hkA; simp at hkA
    have hLeq : (∑ i, a i • d i) = a 0 • oneLp μ := by
      rw [Finset.sum_eq_single (0 : Fin (p + 1))]
      · rw [hd0]
      · intro i _ hi0; rw [hzero_lag i hi0, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLeq] at hL0
    have ha0 : a 0 = 0 := by
      rcases smul_eq_zero.mp hL0 with h | h
      · exact h
      · exact absurd h (oneLp_ne_zero μ)
    funext k
    simp only [Pi.zero_apply]
    rcases eq_or_ne k 0 with rfl | hk
    · exact ha0
    · exact hzero_lag k hk
  set i₀ : Fin (p + 1) := A.min' hA_ne with hi₀_def
  have hi₀A : i₀ ∈ A := A.min'_mem hA_ne
  have ha_i₀ : a i₀ ≠ 0 := ((hmem_A i₀).mp hi₀A).2
  set n : ℕ := i₀.val with hn_def
  have hmem : (hE (0 - (n : ℤ))).toLp ∈ pastSpan pathCoord μ hE (0 - (n : ℤ) - 1) := by
    have hsum_eq : a i₀ • d i₀ + ∑ i ∈ Finset.univ.erase i₀, a i • d i = 0 := by
      rw [Finset.add_sum_erase Finset.univ (fun i => a i • d i) (Finset.mem_univ i₀)]; exact hL0
    have hsplit : a i₀ • d i₀ = -(∑ i ∈ Finset.univ.erase i₀, a i • d i) :=
      eq_neg_of_add_eq_zero_left hsum_eq
    have hterm : ∀ i ∈ Finset.univ.erase i₀,
        a i • d i ∈ pastSpan pathCoord μ hE (0 - (n : ℤ) - 1) := by
      intro i hi
      obtain ⟨hine, -⟩ := Finset.mem_erase.mp hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [hd0]
        exact Submodule.smul_mem _ _ (oneLp_mem_pastSpan _)
      · by_cases hai : a i = 0
        · rw [hai, zero_smul]; exact Submodule.zero_mem _
        · have hiA : i ∈ A := (hmem_A i).mpr ⟨hlag_ne i hi0, hai⟩
          have hlt : i₀ < i := lt_of_le_of_ne (A.min'_le i hiA) (Ne.symm hine)
          have hnlt : n < i.val := Fin.lt_def.mp hlt
          rw [hdi i hi0]
          exact Submodule.smul_mem _ _ (toLp_mem_pastSpan (by omega))
    have hRHS : -(∑ i ∈ Finset.univ.erase i₀, a i • d i)
        ∈ pastSpan pathCoord μ hE (0 - (n : ℤ) - 1) :=
      Submodule.neg_mem _ (Submodule.sum_mem _ hterm)
    have hi₀pos : 1 ≤ i₀.val := ((hmem_A i₀).mp hi₀A).1
    have hi₀0 : i₀ ≠ 0 := by
      intro h; rw [h] at hi₀pos; exact absurd hi₀pos (by simp)
    have hdval : d i₀ = (hE (0 - (n : ℤ))).toLp := by rw [hn_def]; exact hdi i₀ hi₀0
    have hmem_smul : a i₀ • (hE (0 - (n : ℤ))).toLp
        ∈ pastSpan pathCoord μ hE (0 - (n : ℤ) - 1) := by
      rw [← hdval, hsplit]; exact hRHS
    have hrw : (hE (0 - (n : ℤ))).toLp = (a i₀)⁻¹ • (a i₀ • (hE (0 - (n : ℤ))).toLp) := by
      rw [smul_smul, inv_mul_cancel₀ ha_i₀, one_smul]
    rw [hrw]
    exact Submodule.smul_mem _ _ hmem_smul
  -- Step D: the Wold error at that lag vanishes; stationarity carries this to time 0.
  have hwe0 : woldError pathCoord μ hE (0 - (n : ℤ)) = 0 := by
    have hfix : linPred pathCoord μ hE (0 - (n : ℤ) - 1) ((hE (0 - (n : ℤ))).toLp)
        = (hE (0 - (n : ℤ))).toLp := by
      rw [linPred]; exact Submodule.starProjection_eq_self_iff.mpr hmem
    rw [woldError, hfix, sub_self]
  have hnorm := norm_woldError_pathCoord_eq hSS hmeas hE (0 - (n : ℤ))
  rw [hwe0, norm_zero] at hnorm
  unfold projErrorVariance
  rw [← hnorm]; norm_num

/-- **Hansen Theorem 14.28 (identification of the approximating AR(p)).** For a strictly stationary,
square-integrable process that is not purely deterministic (positive one-step prediction-error
variance `σ² > 0`), the design second-moment matrix `Q` is positive definite. The proof never uses
that the AR model is correctly specified, so this is the primary statement; Theorem 14.27
(`arGram_posDef_of_ar`) is its correctly-specified instance.

Positive semidefiniteness is the mean-square identity `a ⬝ᵥ (Q *ᵥ a) = E[(a ⬝ᵥ design)²] ≥ 0`. For
strict definiteness, `a ⬝ᵥ (Q *ᵥ a) = 0` forces `a ⬝ᵥ design = 0` almost surely, an exact linear
dependence among `{1, X_{−1}, …, X_{−p}}` that (via `projErrorVariance_eq_zero_of_ae_dotProduct`)
collapses `σ²` to `0`, contradicting the hypothesis. -/
theorem arGram_posDef [IsProbabilityMeasure P]
    (hSS : IsStrictlyStationary X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hL2 : ∀ s, MemLp (X s) 2 P)
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) (memLp_pathCoord_pathLaw hmeas hL2))
    (p : ℕ) :
    (arGram X P p).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (arGram_isHermitian p) fun a ha => ?_
  simp only [star_trivial]
  rw [dotProduct_arGram_mulVec hL2 p a]
  rcases lt_or_eq_of_le
      (integral_nonneg (f := fun ω => (a ⬝ᵥ arDesign X p 0 ω) ^ 2) fun ω => sq_nonneg _)
      with hpos | hz
  · exact hpos
  · exfalso
    have hmemLin : MemLp (fun ω => a ⬝ᵥ arDesign X p 0 ω) 2 P := by
      have hfun : (fun ω => a ⬝ᵥ arDesign X p 0 ω)
          = ∑ i, fun ω => a i * arDesign X p 0 ω i := by
        funext ω; simp only [Finset.sum_apply]; rfl
      rw [hfun]
      exact memLp_finset_sum' _ fun i _ => (memLp_arDesign hL2 p i).const_mul (a i)
    have hintegrable : Integrable (fun ω => (a ⬝ᵥ arDesign X p 0 ω) ^ 2) P := by
      refine (hmemLin.integrable_mul hmemLin).congr ?_
      filter_upwards with ω; rw [Pi.mul_apply, ← pow_two]
    have hzero : ∫ ω, (a ⬝ᵥ arDesign X p 0 ω) ^ 2 ∂P = 0 := hz.symm
    have hae0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hintegrable).mp hzero
    have hrel : ∀ᵐ ω ∂P, a ⬝ᵥ arDesign X p 0 ω = 0 := by
      filter_upwards [hae0] with ω hω
      simp only [Pi.zero_apply] at hω
      exact (pow_eq_zero_iff (by norm_num)).mp hω
    exact absurd (projErrorVariance_eq_zero_of_ae_dotProduct hSS hmeas hL2 ha hrel) (ne_of_gt hσ)

/-- **The AR(p) projection coefficient vector** `α = Q⁻¹ E[design · X_t]`, anchored at `t = 0`.
This is the canonical name the LS-consistency theorem (14.29) estimates. -/
noncomputable def arProjCoeff (X : ℤ → Ω → ℝ) (P : Measure Ω) (p : ℕ) : Fin (p + 1) → ℝ :=
  (arGram X P p)⁻¹ *ᵥ fun i => ∫ ω, arDesign X p 0 ω i * X 0 ω ∂P

/-- **The normal equations.** Under the identification hypotheses of Theorem 14.28 the projection
coefficient vector solves `Q α = E[design · X_t]`; positive definiteness of `Q` makes it the unique
solution. -/
theorem arGram_mulVec_arProjCoeff [IsProbabilityMeasure P]
    (hSS : IsStrictlyStationary X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hL2 : ∀ s, MemLp (X s) 2 P)
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) (memLp_pathCoord_pathLaw hmeas hL2))
    (p : ℕ) :
    arGram X P p *ᵥ arProjCoeff X P p = fun i => ∫ ω, arDesign X p 0 ω i * X 0 ω ∂P := by
  have hdet : IsUnit (arGram X P p).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (arGram_posDef hSS hmeas hL2 hσ p).isUnit
  rw [arProjCoeff, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **Hansen Theorem 14.27 (identification of a correctly specified AR(p)).** The
correctly-specified instance of Theorem 14.28: the AR hypothesis adds nothing to the Gram argument,
so positive definiteness holds under the same strict-stationarity / square-integrability /
non-degeneracy conditions, and the projection coefficient `arProjCoeff` is identified by the normal
equations `arGram_mulVec_arProjCoeff`. -/
theorem arGram_posDef_of_ar [IsProbabilityMeasure P]
    (hSS : IsStrictlyStationary X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hL2 : ∀ s, MemLp (X s) 2 P)
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) (memLp_pathCoord_pathLaw hmeas hL2))
    (p : ℕ) :
    (arGram X P p).PosDef :=
  arGram_posDef hSS hmeas hL2 hσ p

section LSAsymptotics

open HansenEconometrics
open scoped Matrix.Norms.Elementwise

/-- **The sample AR(p) Gram matrix** (Star convention): `Q̂ₙ = (1/n) ∑_{t<n} design_t design_tᵀ`. -/
noncomputable def arGramHat (X : ℤ → Ω → ℝ) (p : ℕ) (n : ℕ) (ω : Ω) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n,
    Matrix.vecMulVec (arDesign X p (t : ℤ) ω) (arDesign X p (t : ℤ) ω)

/-- **The sample AR(p) cross-moment vector**: `ĉₙ = (1/n) ∑_{t<n} design_t · X_t`. -/
noncomputable def arCrossHat (X : ℤ → Ω → ℝ) (p : ℕ) (n : ℕ) (ω : Ω) : Fin (p + 1) → ℝ :=
  (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, (X (t : ℤ) ω) • arDesign X p (t : ℤ) ω

/-- **The least-squares AR(p) coefficient estimator** in Star form (`Matrix.nonsingInv`):
`α̂ₙ = Q̂ₙ⁻¹ ĉₙ`. -/
noncomputable def arLSStar (X : ℤ → Ω → ℝ) (p : ℕ) (n : ℕ) (ω : Ω) : Fin (p + 1) → ℝ :=
  (arGramHat X p n ω)⁻¹ *ᵥ arCrossHat X p n ω

omit [IsFiniteMeasure P] in
/-- **Ergodic sample-average engine (shared by 14.29 and 14.35(a)).** For an ergodic base process
`Z` and a measurable path functional `φ` whose value at time `0` is integrable, the sample average
of `φ` along the shifted paths converges in probability to `𝔼[φ(history)]`. This is the single
reusable core of least-squares consistency: each entry of `arGramHat`/`arCrossHat` (and of their
time-series-regression analogues) is an instance obtained by choosing a coordinate-selecting `φ`, so
no outer-product/stacking algebra is needed. It packages
`IsErgodicProcess.comp_shiftEquivariant` (Hansen 14.5) with the ergodic theorem in probability
(`IsErgodicProcess.tendstoInMeasure_average`, Hansen 14.9(b)). -/
private theorem tendstoInMeasure_ergodicAverage_pathFunctional [IsProbabilityMeasure P]
    {E : Type*} [MeasurableSpace E] {Z : ℤ → Ω → E}
    (hZe : IsErgodicProcess Z P) (hZmeas : ∀ t, AEMeasurable (Z t) P)
    {φ : (ℤ → E) → ℝ} (hφ : Measurable φ)
    (hint : Integrable (fun ω => φ (fun l => Z (0 + l) ω)) P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, φ (fun l => Z ((t : ℤ) + l) ω))
      atTop (fun _ => ∫ ω, φ (fun l => Z (0 + l) ω) ∂P) := by
  have herg : IsErgodicProcess (fun t ω => φ (fun j => Z (t + j) ω)) P :=
    hZe.comp_shiftEquivariant hφ hZmeas
  have hmeas' : ∀ t, AEMeasurable (fun ω => φ (fun j => Z (t + j) ω)) P := fun t =>
    hφ.comp_aemeasurable (aemeasurable_pi_iff.mpr fun j => hZmeas (t + j))
  exact herg.tendstoInMeasure_average hmeas' hint

/-- The AR(p) design vector written as a functional of a path `y : ℤ → ℝ`:
`(1, y₋₁, …, y₋ₚ)`. Composing with the shifted history recovers `arDesign` (`arDesign_eq_path`),
which is what lets the ergodic engine see the design process as a shift-equivariant functional. -/
private def arDesignPath (p : ℕ) (y : ℤ → ℝ) : Fin (p + 1) → ℝ :=
  fun i => if i = 0 then 1 else y (-(i.val : ℤ))

omit [MeasurableSpace Ω] in
private theorem arDesign_eq_path (X : ℤ → Ω → ℝ) (p : ℕ) (t : ℤ) (ω : Ω) :
    arDesign X p t ω = arDesignPath p (fun l => X (t + l) ω) := by
  funext i
  simp only [arDesign, arDesignPath]
  by_cases h : i = 0
  · simp [h]
  · simp only [if_neg h]; rw [sub_eq_add_neg]

private theorem measurable_arDesignPath_apply (p : ℕ) (i : Fin (p + 1)) :
    Measurable (fun y : ℤ → ℝ => arDesignPath p y i) := by
  by_cases h : i = 0
  · simp only [arDesignPath, if_pos h]; exact measurable_const
  · simp only [arDesignPath, if_neg h]; exact measurable_pi_apply _

/-- Entrywise LLN for the sample Gram: each entry `(i,j)` of `Q̂ₙ` converges in probability to the
population entry `arGram X P p i j`, via the ergodic engine on the coordinate-product functional. -/
private theorem arGramHat_entry_tendsto [IsProbabilityMeasure P]
    (hErg : IsErgodicProcess X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hL2 : ∀ s, MemLp (X s) 2 P) (p : ℕ) (i j : Fin (p + 1)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        arDesign X p (t : ℤ) ω i * arDesign X p (t : ℤ) ω j)
      atTop (fun _ => arGram X P p i j) := by
  have hφ : Measurable (fun y : ℤ → ℝ => arDesignPath p y i * arDesignPath p y j) :=
    (measurable_arDesignPath_apply p i).mul (measurable_arDesignPath_apply p j)
  have hkey : ∀ (s : ℤ) (ω : Ω),
      (fun y : ℤ → ℝ => arDesignPath p y i * arDesignPath p y j) (fun l => X (s + l) ω)
        = arDesign X p s ω i * arDesign X p s ω j := by
    intro s ω
    simp only [← arDesign_eq_path X p s ω]
  have hint : Integrable
      (fun ω => (fun y : ℤ → ℝ => arDesignPath p y i * arDesignPath p y j)
        (fun l => X (0 + l) ω)) P := by
    refine ((memLp_arDesign hL2 p i).integrable_mul (memLp_arDesign hL2 p j)).congr ?_
    filter_upwards with ω
    exact (hkey 0 ω).symm
  have hconv := tendstoInMeasure_ergodicAverage_pathFunctional hErg hmeas hφ hint
  simp only [hkey] at hconv
  exact hconv

omit [MeasurableSpace Ω] [IsFiniteMeasure P] in
/-- Entrywise value of the sample Gram matrix. -/
private theorem arGramHat_apply (X : ℤ → Ω → ℝ) (p n : ℕ) (ω : Ω) (i j : Fin (p + 1)) :
    arGramHat X p n ω i j
      = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
          arDesign X p (t : ℤ) ω i * arDesign X p (t : ℤ) ω j := by
  simp only [arGramHat, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]

/-- **WLLN for the sample AR(p) Gram matrix.** `Q̂ₙ →ₚ Q`. Assembled from the entrywise ergodic LLN
(`arGramHat_entry_tendsto`) by the coordinatewise-to-joint bridge `tendstoInMeasure_pi`, applied
once per matrix index. -/
private theorem arGramHat_tendsto [IsProbabilityMeasure P]
    (hErg : IsErgodicProcess X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hL2 : ∀ s, MemLp (X s) 2 P) (p : ℕ) :
    TendstoInMeasure P (fun n ω => arGramHat X p n ω) atTop (fun _ => arGram X P p) := by
  refine tendstoInMeasure_pi (fun i => tendstoInMeasure_pi (fun j => ?_))
  have hentry := arGramHat_entry_tendsto hErg hmeas hL2 p i j
  refine hentry.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω => ?_
  exact (arGramHat_apply X p n ω i j).symm

/-- Entrywise LLN for the sample cross-moment: coordinate `i` of `ĉₙ` converges in probability to
`𝔼[design_i · X₀]`, via the ergodic engine on the functional `y ↦ arDesignPath p y i · y 0`. -/
private theorem arCrossHat_entry_tendsto [IsProbabilityMeasure P]
    (hErg : IsErgodicProcess X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hL2 : ∀ s, MemLp (X s) 2 P) (p : ℕ) (i : Fin (p + 1)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        arDesign X p (t : ℤ) ω i * X (t : ℤ) ω)
      atTop (fun _ => ∫ ω, arDesign X p 0 ω i * X 0 ω ∂P) := by
  have hφ : Measurable (fun y : ℤ → ℝ => arDesignPath p y i * y 0) :=
    (measurable_arDesignPath_apply p i).mul (measurable_pi_apply 0)
  have hkey : ∀ (s : ℤ) (ω : Ω),
      (fun y : ℤ → ℝ => arDesignPath p y i * y 0) (fun l => X (s + l) ω)
        = arDesign X p s ω i * X s ω := by
    intro s ω
    simp only [← arDesign_eq_path X p s ω, add_zero]
  have hint : Integrable
      (fun ω => (fun y : ℤ → ℝ => arDesignPath p y i * y 0) (fun l => X (0 + l) ω)) P := by
    refine ((memLp_arDesign hL2 p i).integrable_mul (hL2 0)).congr ?_
    filter_upwards with ω
    exact (hkey 0 ω).symm
  have hconv := tendstoInMeasure_ergodicAverage_pathFunctional hErg hmeas hφ hint
  simp only [hkey] at hconv
  exact hconv

omit [MeasurableSpace Ω] [IsFiniteMeasure P] in
/-- Entrywise value of the sample cross-moment vector. -/
private theorem arCrossHat_apply (X : ℤ → Ω → ℝ) (p n : ℕ) (ω : Ω) (i : Fin (p + 1)) :
    arCrossHat X p n ω i
      = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, arDesign X p (t : ℤ) ω i * X (t : ℤ) ω := by
  simp only [arCrossHat, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **WLLN for the sample AR(p) cross-moment.** `ĉₙ →ₚ 𝔼[design · X]`, the RHS of the normal
equations. Assembled entrywise from `arCrossHat_entry_tendsto` by `tendstoInMeasure_pi`. -/
private theorem arCrossHat_tendsto [IsProbabilityMeasure P]
    (hErg : IsErgodicProcess X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hL2 : ∀ s, MemLp (X s) 2 P) (p : ℕ) :
    TendstoInMeasure P (fun n ω => arCrossHat X p n ω) atTop
      (fun _ => fun i => ∫ ω, arDesign X p 0 ω i * X 0 ω ∂P) := by
  refine tendstoInMeasure_pi (fun i => ?_)
  have hentry := arCrossHat_entry_tendsto hErg hmeas hL2 p i
  refine hentry.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω => ?_
  exact (arCrossHat_apply X p n ω i).symm

omit [IsFiniteMeasure P] in
/-- The design vector `ω ↦ (1, X_{t−1}, …, X_{t−p})` is a.e.-strongly measurable. -/
private theorem aestronglyMeasurable_arDesign
    (hmeas : ∀ t, AEMeasurable (X t) P) (p : ℕ) (t : ℤ) :
    AEStronglyMeasurable (fun ω => arDesign X p t ω) P := by
  refine AEMeasurable.aestronglyMeasurable ?_
  rw [aemeasurable_pi_iff]
  intro i
  by_cases h : i = 0
  · simp only [arDesign, if_pos h]; exact aemeasurable_const
  · simp only [arDesign, if_neg h]; exact hmeas _

omit [IsFiniteMeasure P] in
/-- The sample Gram matrix is a.e.-strongly measurable for each `n`. -/
private theorem aestronglyMeasurable_arGramHat
    (hmeas : ∀ t, AEMeasurable (X t) P) (p n : ℕ) :
    AEStronglyMeasurable (fun ω => arGramHat X p n ω) P := by
  simp only [arGramHat]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun t _ => ?_)
  exact (Continuous.matrix_vecMulVec continuous_id continuous_id).comp_aestronglyMeasurable
    (aestronglyMeasurable_arDesign hmeas p (t : ℤ))

omit [IsFiniteMeasure P] in
/-- The sample cross-moment vector is a.e.-strongly measurable for each `n`. -/
private theorem aestronglyMeasurable_arCrossHat
    (hmeas : ∀ t, AEMeasurable (X t) P) (p n : ℕ) :
    AEStronglyMeasurable (fun ω => arCrossHat X p n ω) P := by
  simp only [arCrossHat]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun t _ => ?_)
  exact ((hmeas (t : ℤ)).aestronglyMeasurable).smul (aestronglyMeasurable_arDesign hmeas p (t : ℤ))

/-- **Hansen Theorem 14.29 (least-squares consistency for an AR(p)).** For a strictly stationary,
ergodic, square-integrable process that is not purely deterministic (positive one-step
prediction-error variance `σ² > 0`), the least-squares estimator of the best linear AR(p) predictor
is consistent: `α̂ₙ →ₚ α`, where `α = arProjCoeff X P p = Q⁻¹ 𝔼[design · X]`.

The hypotheses are exactly those of the identification theorem `arGram_posDef` (14.28) together with
ergodicity `hErg` (which the ergodic theorem consumes). The proof routes the entrywise ergodic LLN
through the matrix continuous-mapping algebra: `arGramHat_tendsto` gives `Q̂ₙ →ₚ Q` and
`arCrossHat_tendsto` gives `ĉₙ →ₚ 𝔼[design · X]`; positive definiteness of `Q` (14.28) makes its
determinant a unit, so `tendstoInMeasure_matrix_inv` gives `Q̂ₙ⁻¹ →ₚ Q⁻¹`, and
`tendstoInMeasure_mulVec` composes to `Q̂ₙ⁻¹ ĉₙ →ₚ Q⁻¹ 𝔼[design · X] = α`. Variance estimation
(`σ̂²`) is deferred to Hansen's Theorem 14.33 (covariance-matrix estimation). -/
theorem arLS_consistent [IsProbabilityMeasure P]
    (hSS : IsStrictlyStationary X P) (hErg : IsErgodicProcess X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hL2 : ∀ s, MemLp (X s) 2 P)
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) (memLp_pathCoord_pathLaw hmeas hL2))
    (p : ℕ) :
    TendstoInMeasure P (fun n ω => arLSStar X p n ω) atTop (fun _ => arProjCoeff X P p) := by
  have hdet : IsUnit (arGram X P p).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (arGram_posDef hSS hmeas hL2 hσ p).isUnit
  have hInv := tendstoInMeasure_matrix_inv
    (fun n => aestronglyMeasurable_arGramHat hmeas p n) (arGramHat_tendsto hErg hmeas hL2 p)
    (fun _ => hdet)
  have hInv_meas : ∀ n, AEStronglyMeasurable (fun ω => (arGramHat X p n ω)⁻¹) P :=
    fun n => aestronglyMeasurable_matrix_inv (aestronglyMeasurable_arGramHat hmeas p n)
  exact tendstoInMeasure_mulVec hInv_meas
    (fun n => aestronglyMeasurable_arCrossHat hmeas p n) hInv (arCrossHat_tendsto hErg hmeas hL2 p)

/-! ### Theorem 14.35(a): consistency of a general time-series regression

The AR(p) argument depends only on the shared ergodic-average engine, so the same skeleton proves
consistency of a generic time-series regression. We encode the joint `(outcome, regressors)` process
as a single `(Fin (k+1) → ℝ)`-valued process `Z`, with coordinate `0` the outcome `Yₜ` and
coordinates `1, …, k` the regressors `Xₜ`. The regression coefficient is `β = Q⁻¹ 𝔼[Xₜ Yₜ]` with
`Q = 𝔼[Xₜ Xₜᵀ]`, and its least-squares estimator `β̂ₙ = Q̂ₙ⁻¹ ĉₙ` is consistent. Parts (b) and (c)
(asymptotic normality under a martingale-difference or mixing score) are deferred to later work
packages, which extend `TSRegressionConditions` with the relevant CLT bundle. -/

variable {k : ℕ}

/-- Population regressor Gram `Q = 𝔼[Xₜ Xₜᵀ]` of the joint process (regressors are coordinates
`1, …, k`). -/
noncomputable def tsGram (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (P : Measure Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∫ ω, Z 0 ω i.succ * Z 0 ω j.succ ∂P

/-- Population cross-moment `𝔼[Xₜ Yₜ]` (outcome is coordinate `0`). -/
noncomputable def tsCross (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (P : Measure Ω) : Fin k → ℝ :=
  fun i => ∫ ω, Z 0 ω i.succ * Z 0 ω 0 ∂P

/-- Population regression coefficient `β = Q⁻¹ 𝔼[Xₜ Yₜ]`. -/
noncomputable def tsBeta (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (P : Measure Ω) : Fin k → ℝ :=
  (tsGram Z P)⁻¹ *ᵥ tsCross Z P

/-- Sample regressor Gram `Q̂ₙ = (1/n) ∑_{t<n} Xₜ Xₜᵀ`. -/
noncomputable def tsGramHat (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (n : ℕ) (ω : Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n,
    Matrix.vecMulVec (fun i => Z (t : ℤ) ω i.succ) (fun i => Z (t : ℤ) ω i.succ)

/-- Sample cross-moment `ĉₙ = (1/n) ∑_{t<n} Xₜ Yₜ`. -/
noncomputable def tsCrossHat (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (n : ℕ) (ω : Ω) : Fin k → ℝ :=
  (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, (Z (t : ℤ) ω 0) • (fun i => Z (t : ℤ) ω i.succ)

/-- Least-squares estimator `β̂ₙ = Q̂ₙ⁻¹ ĉₙ` (Star form). -/
noncomputable def tsBetaStar (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (n : ℕ) (ω : Ω) : Fin k → ℝ :=
  (tsGramHat Z n ω)⁻¹ *ᵥ tsCrossHat Z n ω

/-- **Standing hypotheses for a time-series regression** (Hansen 14.35). The joint
`(outcome, regressors)` process `Z` is strictly stationary and ergodic with square-integrable
coordinates, and the population regressor Gram is positive definite. These are the conditions under
which the least-squares estimator is consistent; parts (b)/(c) extend this bundle with a CLT
condition on the score. -/
structure TSRegressionConditions (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (P : Measure Ω) : Prop where
  /-- Strict stationarity of the joint process. -/
  stationary : IsStrictlyStationary Z P
  /-- Ergodicity of the joint process (consumed by the ergodic theorem). -/
  ergodic : IsErgodicProcess Z P
  /-- Coordinate measurability. -/
  meas : ∀ t, AEMeasurable (Z t) P
  /-- Square integrability of every coordinate. -/
  memLp : ∀ (t : ℤ) (i : Fin (k + 1)), MemLp (fun ω => Z t ω i) 2 P
  /-- Positive definiteness of the population regressor Gram. -/
  posDef : (tsGram Z P).PosDef

omit [IsFiniteMeasure P] in
/-- Entrywise LLN for the sample regressor Gram. -/
private theorem tsGramHat_entry_tendsto [IsProbabilityMeasure P]
    {Z : ℤ → Ω → (Fin (k + 1) → ℝ)} (h : TSRegressionConditions Z P) (i j : Fin k) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        Z (t : ℤ) ω i.succ * Z (t : ℤ) ω j.succ)
      atTop (fun _ => tsGram Z P i j) := by
  have hφ : Measurable (fun y : ℤ → (Fin (k + 1) → ℝ) => y 0 i.succ * y 0 j.succ) :=
    ((measurable_pi_apply i.succ).comp (measurable_pi_apply 0)).mul
      ((measurable_pi_apply j.succ).comp (measurable_pi_apply 0))
  have hkey : ∀ (s : ℤ) (ω : Ω),
      (fun y : ℤ → (Fin (k + 1) → ℝ) => y 0 i.succ * y 0 j.succ) (fun l => Z (s + l) ω)
        = Z s ω i.succ * Z s ω j.succ := by
    intro s ω; simp only [add_zero]
  have hint : Integrable
      (fun ω => (fun y : ℤ → (Fin (k + 1) → ℝ) => y 0 i.succ * y 0 j.succ)
        (fun l => Z (0 + l) ω)) P := by
    refine ((h.memLp 0 i.succ).integrable_mul (h.memLp 0 j.succ)).congr ?_
    filter_upwards with ω; exact (hkey 0 ω).symm
  have hconv := tendstoInMeasure_ergodicAverage_pathFunctional h.ergodic h.meas hφ hint
  simp only [hkey] at hconv
  exact hconv

omit [MeasurableSpace Ω] [IsFiniteMeasure P] in
/-- Entrywise value of the sample regressor Gram. -/
private theorem tsGramHat_apply (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (n : ℕ) (ω : Ω) (i j : Fin k) :
    tsGramHat Z n ω i j
      = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, Z (t : ℤ) ω i.succ * Z (t : ℤ) ω j.succ := by
  simp only [tsGramHat, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]

omit [IsFiniteMeasure P] in
/-- **WLLN for the sample regressor Gram.** `Q̂ₙ →ₚ Q`. -/
private theorem tsGramHat_tendsto [IsProbabilityMeasure P]
    {Z : ℤ → Ω → (Fin (k + 1) → ℝ)} (h : TSRegressionConditions Z P) :
    TendstoInMeasure P (fun n ω => tsGramHat Z n ω) atTop (fun _ => tsGram Z P) := by
  refine tendstoInMeasure_pi (fun i => tendstoInMeasure_pi (fun j => ?_))
  refine (tsGramHat_entry_tendsto h i j).congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω => ?_
  exact (tsGramHat_apply Z n ω i j).symm

omit [IsFiniteMeasure P] in
/-- Entrywise LLN for the sample cross-moment. -/
private theorem tsCrossHat_entry_tendsto [IsProbabilityMeasure P]
    {Z : ℤ → Ω → (Fin (k + 1) → ℝ)} (h : TSRegressionConditions Z P) (i : Fin k) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        Z (t : ℤ) ω i.succ * Z (t : ℤ) ω 0)
      atTop (fun _ => tsCross Z P i) := by
  have hφ : Measurable (fun y : ℤ → (Fin (k + 1) → ℝ) => y 0 i.succ * y 0 0) :=
    ((measurable_pi_apply i.succ).comp (measurable_pi_apply 0)).mul
      ((measurable_pi_apply 0).comp (measurable_pi_apply 0))
  have hkey : ∀ (s : ℤ) (ω : Ω),
      (fun y : ℤ → (Fin (k + 1) → ℝ) => y 0 i.succ * y 0 0) (fun l => Z (s + l) ω)
        = Z s ω i.succ * Z s ω 0 := by
    intro s ω; simp only [add_zero]
  have hint : Integrable
      (fun ω => (fun y : ℤ → (Fin (k + 1) → ℝ) => y 0 i.succ * y 0 0)
        (fun l => Z (0 + l) ω)) P := by
    refine ((h.memLp 0 i.succ).integrable_mul (h.memLp 0 0)).congr ?_
    filter_upwards with ω; exact (hkey 0 ω).symm
  have hconv := tendstoInMeasure_ergodicAverage_pathFunctional h.ergodic h.meas hφ hint
  simp only [hkey] at hconv
  exact hconv

omit [MeasurableSpace Ω] [IsFiniteMeasure P] in
/-- Entrywise value of the sample cross-moment. -/
private theorem tsCrossHat_apply (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (n : ℕ) (ω : Ω) (i : Fin k) :
    tsCrossHat Z n ω i
      = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, Z (t : ℤ) ω i.succ * Z (t : ℤ) ω 0 := by
  simp only [tsCrossHat, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [IsFiniteMeasure P] in
/-- **WLLN for the sample cross-moment.** `ĉₙ →ₚ 𝔼[Xₜ Yₜ]`. -/
private theorem tsCrossHat_tendsto [IsProbabilityMeasure P]
    {Z : ℤ → Ω → (Fin (k + 1) → ℝ)} (h : TSRegressionConditions Z P) :
    TendstoInMeasure P (fun n ω => tsCrossHat Z n ω) atTop (fun _ => tsCross Z P) := by
  refine tendstoInMeasure_pi (fun i => ?_)
  refine (tsCrossHat_entry_tendsto h i).congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun ω => ?_
  exact (tsCrossHat_apply Z n ω i).symm

omit [IsFiniteMeasure P] in
/-- The regressor vector `ω ↦ (X_{t,1}, …, X_{t,k})` is a.e.-strongly measurable. -/
private theorem aestronglyMeasurable_tsRegressors
    {Z : ℤ → Ω → (Fin (k + 1) → ℝ)} (h : TSRegressionConditions Z P) (t : ℤ) :
    AEStronglyMeasurable (fun ω => (fun i => Z t ω i.succ : Fin k → ℝ)) P := by
  refine AEMeasurable.aestronglyMeasurable ?_
  rw [aemeasurable_pi_iff]
  exact fun i => (measurable_pi_apply i.succ).comp_aemeasurable (h.meas t)

omit [IsFiniteMeasure P] in
/-- The sample regressor Gram is a.e.-strongly measurable for each `n`. -/
private theorem aestronglyMeasurable_tsGramHat
    {Z : ℤ → Ω → (Fin (k + 1) → ℝ)} (h : TSRegressionConditions Z P) (n : ℕ) :
    AEStronglyMeasurable (fun ω => tsGramHat Z n ω) P := by
  simp only [tsGramHat]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun t _ => ?_)
  exact (Continuous.matrix_vecMulVec continuous_id continuous_id).comp_aestronglyMeasurable
    (aestronglyMeasurable_tsRegressors h (t : ℤ))

omit [IsFiniteMeasure P] in
/-- The sample cross-moment is a.e.-strongly measurable for each `n`. -/
private theorem aestronglyMeasurable_tsCrossHat
    {Z : ℤ → Ω → (Fin (k + 1) → ℝ)} (h : TSRegressionConditions Z P) (n : ℕ) :
    AEStronglyMeasurable (fun ω => tsCrossHat Z n ω) P := by
  simp only [tsCrossHat]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun t _ => ?_)
  exact (((measurable_pi_apply 0).comp_aemeasurable (h.meas (t : ℤ))).aestronglyMeasurable).smul
    (aestronglyMeasurable_tsRegressors h (t : ℤ))

/-- **Hansen Theorem 14.35(a) (consistency of a time-series regression).** Under the standing
`TSRegressionConditions` — strict stationarity, ergodicity, square integrability, and a positive
definite population regressor Gram — the least-squares estimator is consistent:
`β̂ₙ →ₚ β = Q⁻¹ 𝔼[Xₜ Yₜ]`. The proof is the AR(p) skeleton (`arLS_consistent`) with a generic
design: it reuses the shared ergodic-average engine `tendstoInMeasure_ergodicAverage_pathFunctional`
for the entrywise LLNs, then the matrix continuous-mapping algebra (`tendstoInMeasure_matrix_inv`,
`tendstoInMeasure_mulVec`). Parts (b) and (c) (asymptotic normality under a martingale-difference or
mixing score) are deferred to later work packages. -/
theorem tsRegression_consistent [IsProbabilityMeasure P]
    {Z : ℤ → Ω → (Fin (k + 1) → ℝ)} (h : TSRegressionConditions Z P) :
    TendstoInMeasure P (fun n ω => tsBetaStar Z n ω) atTop (fun _ => tsBeta Z P) := by
  have hdet : IsUnit (tsGram Z P).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h.posDef.isUnit
  have hInv := tendstoInMeasure_matrix_inv (fun n => aestronglyMeasurable_tsGramHat h n)
    (tsGramHat_tendsto h) (fun _ => hdet)
  have hInv_meas : ∀ n, AEStronglyMeasurable (fun ω => (tsGramHat Z n ω)⁻¹) P :=
    fun n => aestronglyMeasurable_matrix_inv (aestronglyMeasurable_tsGramHat h n)
  exact tendstoInMeasure_mulVec hInv_meas (fun n => aestronglyMeasurable_tsCrossHat h n) hInv
    (tsCrossHat_tendsto h)

/-! ### Theorems 14.30 and 14.31: asymptotic normality of the AR(p) least-squares estimator

Under correct specification `Yₜ = xₜ ⬝ α + eₜ` (design
`xₜ = arDesign Y p t = (1, Y_{t−1}, …, Y_{t−p})`, true coefficient vector `coeff = (α₀, α₁, …, αₚ)`)
with `Y` adapted to the information filtration `ℱ` and `e` a martingale difference sequence, the
least-squares estimator `α̂ₙ = arLSStar Y p n` is asymptotically normal. The single missing analytic
input — the martingale-difference central limit theorem (Hansen 14.11) — is carried by the vector
bundle `MDSCLTConditionsVec` on the score process `uₜ = eₜ • xₜ`, so these theorems are
bundle-conditional in exactly the sense of the campaign design. -/

/-- **Hypotheses of Hansen Theorem 14.30 (correctly specified AR(p)).** The observed process `Y`
satisfies the AR(p) recursion `Yₜ = xₜ ⬝ coeff + eₜ` a.e. (design `xₜ = arDesign Y p t`, true
coefficient vector `coeff`), `Y` is adapted to the information filtration `ℱ`, the innovation `e` is
a martingale difference sequence relative to `ℱ`, `Y` is ergodic with square-integrable coordinates,
and the population design Gram `Q = arGram Y P p` is positive definite (Hansen's identification
condition, Theorem 14.28). The coefficient vector is a parameter rather than a field so the bundle
stays a `Prop`. -/
structure ARModelConditions (Y e : ℤ → Ω → ℝ) (ℱ : Filtration ℤ ‹MeasurableSpace Ω›)
    (P : Measure Ω) (p : ℕ) (coeff : Fin (p + 1) → ℝ) : Prop where
  /-- `Y` is adapted to the information filtration, so `Y_{t−j}` is `ℱ_{t−1}`-measurable for
  `j ≥ 1`. -/
  adapted : Adapted ℱ Y
  /-- The innovation `e` is a martingale difference sequence relative to `ℱ`. -/
  emds : IsMDS ℱ e P
  /-- **Correct specification.** The AR(p) recursion `Yₜ = xₜ ⬝ coeff + eₜ` holds a.e. -/
  recursion : ∀ t, Y t =ᵐ[P] fun ω => arDesign Y p t ω ⬝ᵥ coeff + e t ω
  /-- `Y` is ergodic (consumed by the ergodic LLN giving `Q̂ₙ →ₚ Q`). -/
  ergodic : IsErgodicProcess Y P
  /-- Coordinate measurability of `Y`. -/
  meas : ∀ t, AEMeasurable (Y t) P
  /-- Square integrability of `Y`. -/
  memLp : ∀ s, MemLp (Y s) 2 P
  /-- **Identification (Theorem 14.28).** The population design Gram `Q = arGram Y P p` is positive
  definite. -/
  gram_posDef : (arGram Y P p).PosDef

section AsymptoticNormality

variable {Y e : ℤ → Ω → ℝ} {ℱ : Filtration ℤ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {p : ℕ} {coeff : Fin (p + 1) → ℝ}

/-- Each design coordinate at an arbitrary time `t` is square integrable. -/
private theorem memLp_arDesign_at (hmemLp : ∀ s, MemLp (Y s) 2 P) (p : ℕ) (t : ℤ)
    (i : Fin (p + 1)) : MemLp (fun ω => arDesign Y p t ω i) 2 P := by
  by_cases h : i = 0
  · simp only [arDesign, if_pos h]; exact memLp_const 1
  · simp only [arDesign, if_neg h]; exact hmemLp _

/-- The linear form `xₜ ⬝ a` of the design is square integrable (a finite sum of `L²` coordinates).
-/
private theorem memLp_dotProduct_arDesign (hmemLp : ∀ s, MemLp (Y s) 2 P) (p : ℕ) (t : ℤ)
    (a : Fin (p + 1) → ℝ) : MemLp (fun ω => arDesign Y p t ω ⬝ᵥ a) 2 P := by
  have hrw : (fun ω => arDesign Y p t ω ⬝ᵥ a) = ∑ i, fun ω => arDesign Y p t ω i * a i := by
    funext ω; simp only [Finset.sum_apply, dotProduct]
  rw [hrw]
  exact memLp_finset_sum' _ fun i _ => (memLp_arDesign_at hmemLp p t i).mul_const (a i)

/-- The innovation `eₜ` is square integrable: by the recursion it is a.e. `Yₜ − xₜ ⬝ coeff`, a
difference of `L²` functions. -/
private theorem memLp_e (hrec : Y t =ᵐ[P] fun ω => arDesign Y p t ω ⬝ᵥ coeff + e t ω)
    (hmemLp : ∀ s, MemLp (Y s) 2 P) : MemLp (e t) 2 P := by
  have hdesign : MemLp (fun ω => arDesign Y p t ω ⬝ᵥ coeff) 2 P :=
    memLp_dotProduct_arDesign hmemLp p t coeff
  have he_eq : e t =ᵐ[P] fun ω => Y t ω - arDesign Y p t ω ⬝ᵥ coeff := by
    filter_upwards [hrec] with ω hω; rw [hω]; ring
  exact MemLp.ae_eq he_eq.symm ((hmemLp t).sub hdesign)

/-- The design linear form `xₜ ⬝ a` is `ℱ_{t−1}`-strongly-measurable: the intercept is constant and
each lag `Y_{t−i}` (`i ≥ 1`) is `ℱ_{t−i}`-measurable, hence `ℱ_{t−1}`-measurable. This is the
adaptedness that makes the score `eₜ (xₜ ⬝ a)` a martingale difference. -/
private theorem stronglyMeasurable_dotProduct_arDesign (hY : Adapted ℱ Y) (p : ℕ) (t : ℤ)
    (a : Fin (p + 1) → ℝ) : StronglyMeasurable[ℱ (t - 1)] (fun ω => arDesign Y p t ω ⬝ᵥ a) := by
  classical
  refine Measurable.stronglyMeasurable ?_
  simp only [dotProduct]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.mul_const ?_ (a i)
  by_cases hi : i = 0
  · simp only [arDesign, if_pos hi]; exact measurable_const
  · have hi1 : 1 ≤ (i : ℕ) := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
      · exact absurd (Fin.ext h0) hi
      · exact h0
    have hle : t - ((i : ℕ) : ℤ) ≤ t - 1 := by
      have : (1 : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast hi1
      omega
    simp only [arDesign, if_neg hi]
    exact (hY (t - ((i : ℕ) : ℤ))).mono (ℱ.mono hle) le_rfl

/-- **The score is a martingale difference sequence (Hansen §14.30).** For every direction `a`, the
projected score `t ↦ (eₜ • xₜ) ⬝ a = eₜ (xₜ ⬝ a)` is a martingale difference sequence relative to
the information filtration `ℱ`: the design linear form `xₜ ⬝ a` is `ℱ_{t−1}`-measurable and `eₜ` is
an MDS, so the pull-out property leaves `E[eₜ (xₜ ⬝ a) | ℱ_{t−1}] = (xₜ ⬝ a) E[eₜ | ℱ_{t−1}] = 0`.
This mirrors the pull-out in `ProbabilityTheory.IsMDS.covariance_eq_zero` and is what makes the
score CLT bundle `MDSCLTConditionsVec` applicable. -/
theorem scoreIsMDS (h : ARModelConditions Y e ℱ P p coeff) (a : Fin (p + 1) → ℝ) :
    IsMDS ℱ (fun t ω => (e t ω • arDesign Y p t ω) ⬝ᵥ a) P where
  adapted t := by
    have hg : Measurable[ℱ t] (fun ω => arDesign Y p t ω ⬝ᵥ a) :=
      ((stronglyMeasurable_dotProduct_arDesign h.adapted p t a).measurable).mono
        (ℱ.mono (by omega)) le_rfl
    simp only [smul_dotProduct, smul_eq_mul]
    exact (h.emds.adapted t).mul hg
  integrable t := by
    have hg : MemLp (fun ω => arDesign Y p t ω ⬝ᵥ a) 2 P :=
      memLp_dotProduct_arDesign h.memLp p t a
    have hint : Integrable (fun ω => arDesign Y p t ω ⬝ᵥ a * e t ω) P :=
      hg.integrable_mul (memLp_e (h.recursion t) h.memLp)
    refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [smul_dotProduct, smul_eq_mul]; ring
  condExp_eq_zero t := by
    have hg_sm : StronglyMeasurable[ℱ (t - 1)] (fun ω => arDesign Y p t ω ⬝ᵥ a) :=
      stronglyMeasurable_dotProduct_arDesign h.adapted p t a
    have hg : MemLp (fun ω => arDesign Y p t ω ⬝ᵥ a) 2 P :=
      memLp_dotProduct_arDesign h.memLp p t a
    have hprod_int : Integrable ((fun ω => arDesign Y p t ω ⬝ᵥ a) * e t) P :=
      hg.integrable_mul (memLp_e (h.recursion t) h.memLp)
    have hrw : (fun ω => (e t ω • arDesign Y p t ω) ⬝ᵥ a)
        = (fun ω => arDesign Y p t ω ⬝ᵥ a) * e t := by
      funext ω; simp only [Pi.mul_apply, smul_dotProduct, smul_eq_mul]; ring
    rw [hrw]
    refine (condExp_mul_of_stronglyMeasurable_left hg_sm hprod_int (h.emds.integrable t)).trans ?_
    filter_upwards [h.emds.condExp_eq_zero t] with ω hω
    simp only [Pi.mul_apply, hω, Pi.zero_apply, mul_zero]

omit [IsProbabilityMeasure P] in
/-- **Score-average bridge (Hansen §14.30).** Substituting the AR(p) recursion
`Yₜ = xₜ ⬝ coeff + eₜ` into the sample cross-moment `ĉₙ = (1/n) ∑_{t<n} Yₜ • xₜ` splits it a.e. as
`ĉₙ = Q̂ₙ *ᵥ coeff + (1/n) ∑_{t<n} eₜ • xₜ`: the deterministic regression part is exactly the sample
Gram acting on `coeff`, and the remainder is the score average. This is the identity that converts
`√n(α̂ₙ − coeff)` into `Q̂ₙ⁻¹ · (√n · score-average)`. -/
private theorem arCrossHat_ae_eq (h : ARModelConditions Y e ℱ P p coeff) (n : ℕ) :
    arCrossHat Y p n =ᵐ[P] fun ω => arGramHat Y p n ω *ᵥ coeff
      + (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, e t ω • arDesign Y p t ω := by
  have hrec : ∀ᵐ ω ∂P, ∀ t ∈ Finset.range n,
      Y t ω = arDesign Y p t ω ⬝ᵥ coeff + e t ω := by
    simp only [eventually_all_finset]
    intro t _
    exact h.recursion t
  filter_upwards [hrec] with ω hω
  simp only [arCrossHat, arGramHat, smul_mulVec, sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  rw [← smul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun t ht => ?_)
  rw [← add_smul, ← hω t ht]

/-- **Identification of the AR(p) coefficient under correct specification (Hansen §14.30).** The
best-linear-predictor coefficient equals the structural coefficient: `arProjCoeff Y P p = coeff`.
The projection solves the normal equations `Q · arProjCoeff = 𝔼[x₀ Y₀]`; correct specification
(`Y₀ = x₀ ⬝ coeff + e₀`) together with the martingale-difference orthogonality `𝔼[x₀ e₀] = 0`
collapses `𝔼[x₀ Y₀] = Q · coeff`, so invertibility of `Q` (Theorem 14.28) forces
`arProjCoeff = coeff`. -/
theorem arProjCoeff_eq_coeff (h : ARModelConditions Y e ℱ P p coeff) :
    arProjCoeff Y P p = coeff := by
  have hdet : IsUnit (arGram Y P p).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h.gram_posDef.isUnit
  -- Coordinatewise orthogonality `𝔼[x₀ᵢ e₀] = 0` from the score martingale-difference property.
  have hXe : ∀ i, ∫ ω, arDesign Y p 0 ω i * e 0 ω ∂P = 0 := by
    intro i
    have hmds := (scoreIsMDS h (Pi.single i 1)).integral_eq_zero 0
    rw [← hmds]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul]
    ring
  -- The cross-moment vector `𝔼[x₀ Y₀]` equals `Q · coeff`.
  have hc : (fun i => ∫ ω, arDesign Y p 0 ω i * Y 0 ω ∂P) = arGram Y P p *ᵥ coeff := by
    funext i
    have hInt_dd : Integrable
        (fun ω => arDesign Y p 0 ω i * (arDesign Y p 0 ω ⬝ᵥ coeff)) P :=
      (memLp_arDesign_at h.memLp p 0 i).integrable_mul (memLp_dotProduct_arDesign h.memLp p 0 coeff)
    have hInt_de : Integrable (fun ω => arDesign Y p 0 ω i * e 0 ω) P :=
      (memLp_arDesign_at h.memLp p 0 i).integrable_mul (memLp_e (h.recursion 0) h.memLp)
    have hQv : (arGram Y P p *ᵥ coeff) i
        = ∫ ω, arDesign Y p 0 ω i * (arDesign Y p 0 ω ⬝ᵥ coeff) ∂P := by
      have hint : ∀ j : Fin (p + 1),
          Integrable (fun ω => arDesign Y p 0 ω i * arDesign Y p 0 ω j * coeff j) P :=
        fun j => ((memLp_arDesign_at h.memLp p 0 i).integrable_mul
          (memLp_arDesign_at h.memLp p 0 j)).mul_const _
      rw [mulVec, dotProduct]
      simp only [arGram]
      rw [show (∑ j, (∫ ω, arDesign Y p 0 ω i * arDesign Y p 0 ω j ∂P) * coeff j)
            = ∑ j, ∫ ω, arDesign Y p 0 ω i * arDesign Y p 0 ω j * coeff j ∂P from
          Finset.sum_congr rfl fun j _ => by rw [integral_mul_const]]
      rw [← integral_finset_sum _ (fun j _ => hint j)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hQv]
    calc ∫ ω, arDesign Y p 0 ω i * Y 0 ω ∂P
        = ∫ ω, arDesign Y p 0 ω i * (arDesign Y p 0 ω ⬝ᵥ coeff)
            + arDesign Y p 0 ω i * e 0 ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [h.recursion 0] with ω hω
          rw [hω]; ring
      _ = (∫ ω, arDesign Y p 0 ω i * (arDesign Y p 0 ω ⬝ᵥ coeff) ∂P)
            + ∫ ω, arDesign Y p 0 ω i * e 0 ω ∂P := integral_add hInt_dd hInt_de
      _ = ∫ ω, arDesign Y p 0 ω i * (arDesign Y p 0 ω ⬝ᵥ coeff) ∂P := by rw [hXe i, add_zero]
  rw [arProjCoeff, hc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

omit [IsProbabilityMeasure P] in
/-- Measurability of the score `uₜ = eₜ xₜ` at each time. -/
private theorem aemeasurable_score (h : ARModelConditions Y e ℱ P p coeff) (t : ℤ) :
    AEMeasurable (fun ω => e t ω • arDesign Y p t ω) P :=
  ((h.emds.integrable t).aemeasurable).smul (aestronglyMeasurable_arDesign h.meas p t).aemeasurable

/-- **Score tightness from stationarity (Hansen §14.30).** Under strict stationarity of `Y`, the
score `uₜ = eₜ xₜ` is bounded in probability (`Oₚ(1)`). Correct specification writes `uₜ` as the
a.e. image of a shift-equivariant functional of the `Y`-path (`wₜ = (Yₜ − xₜ⬝coeff) xₜ`), so
`comp_shiftEquivariant` (Theorem 14.2) makes its single-time marginals coincide; the common tail
`P{‖u₀‖ ≥ M}` vanishes as `M → ∞`, giving the uniform-in-`n` tightness bound. This discharges the
`(√n)⁻¹ uₙ` boundary term in the score central limit theorem. -/
private theorem score_boundedInProbabilityNorm (h : ARModelConditions Y e ℱ P p coeff)
    (hstat : IsStrictlyStationary Y P) :
    BoundedInProbabilityNorm P (fun n ω => e (n : ℤ) ω • arDesign Y p (n : ℤ) ω) := by
  classical
  -- Correct specification writes the score as an a.e. image of the recursion-RHS functional
  -- `W y = (y₀ − x(y)⬝coeff) x(y)` of the `Y`-path, which is a shift-equivariant functional of `Y`.
  set W : (ℤ → ℝ) → (Fin (p + 1) → ℝ) :=
    fun y => (y 0 - arDesignPath p y ⬝ᵥ coeff) • arDesignPath p y with hW
  have hWmeas : Measurable W := by
    rw [hW]
    refine measurable_pi_iff.mpr fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    refine Measurable.mul ((measurable_pi_apply 0).sub ?_) (measurable_arDesignPath_apply p i)
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun k _ =>
      (measurable_arDesignPath_apply p k).mul_const (coeff k)
  set Wpath : ℤ → Ω → (Fin (p + 1) → ℝ) := fun t ω => W (fun j => Y (t + j) ω) with hWpath
  have hstatW : IsStrictlyStationary Wpath P := by
    rw [hWpath]; exact hstat.comp_shiftEquivariant hWmeas h.meas
  -- The score `uₜ = eₜ xₜ` is a.e. equal to `Wpath t`.
  have hwscore : ∀ t : ℤ, (fun ω => e t ω • arDesign Y p t ω) =ᵐ[P] Wpath t := by
    intro t
    filter_upwards [h.recursion t] with ω hrec
    have hpath : arDesignPath p (fun j => Y (t + j) ω) = arDesign Y p t ω :=
      (arDesign_eq_path Y p t ω).symm
    change e t ω • arDesign Y p t ω = Wpath t ω
    rw [hWpath, hW]
    simp only [add_zero, hpath, hrec]
    rw [show arDesign Y p t ω ⬝ᵥ coeff + e t ω - arDesign Y p t ω ⬝ᵥ coeff = e t ω from by ring]
  -- Single-time marginals of `Wpath` coincide (strict stationarity, Theorem 14.2).
  have hID_w : ∀ m : ℤ, IdentDistrib (Wpath m) (Wpath 0) P P := by
    intro m
    have hmem : (0 : ℤ) ∈ ({0} : Finset ℤ) := Finset.mem_singleton.mpr rfl
    have hcomp := (hstatW {0} m).comp
      (u := fun f : ({0} : Finset ℤ) → (Fin (p + 1) → ℝ) => f ⟨0, hmem⟩)
      (measurable_pi_apply _)
    have e1 : ((fun f : ({0} : Finset ℤ) → (Fin (p + 1) → ℝ) => f ⟨0, hmem⟩) ∘
        fun ω => ({0} : Finset ℤ).restrict (fun t => Wpath (t + m) ω)) = Wpath m := by
      funext ω; change Wpath (0 + m) ω = Wpath m ω; rw [zero_add]
    have e2 : ((fun f : ({0} : Finset ℤ) → (Fin (p + 1) → ℝ) => f ⟨0, hmem⟩) ∘
        fun ω => ({0} : Finset ℤ).restrict (fun t => Wpath t ω)) = Wpath 0 := by
      funext ω; rfl
    rw [e1, e2] at hcomp
    exact hcomp
  -- Tail probabilities are uniform in `m`: identical distribution collapses the index to `0`.
  have huniform : ∀ (c : ℝ) (m : ℤ),
      P {ω | c ≤ ‖e m ω • arDesign Y p m ω‖} = P {ω | c ≤ ‖e 0 ω • arDesign Y p 0 ω‖} := by
    intro c m
    have hset : MeasurableSet {x : Fin (p + 1) → ℝ | c ≤ ‖x‖} :=
      measurableSet_le measurable_const measurable_norm
    have hcm : P {ω | c ≤ ‖e m ω • arDesign Y p m ω‖} = P {ω | c ≤ ‖Wpath m ω‖} := by
      refine measure_congr ?_
      filter_upwards [hwscore m] with ω hω
      change (c ≤ ‖e m ω • arDesign Y p m ω‖) = (c ≤ ‖Wpath m ω‖)
      rw [show e m ω • arDesign Y p m ω = Wpath m ω from hω]
    have hc0 : P {ω | c ≤ ‖e 0 ω • arDesign Y p 0 ω‖} = P {ω | c ≤ ‖Wpath 0 ω‖} := by
      refine measure_congr ?_
      filter_upwards [hwscore 0] with ω hω
      change (c ≤ ‖e 0 ω • arDesign Y p 0 ω‖) = (c ≤ ‖Wpath 0 ω‖)
      rw [show e 0 ω • arDesign Y p 0 ω = Wpath 0 ω from hω]
    have hmid : P {ω | c ≤ ‖Wpath m ω‖} = P {ω | c ≤ ‖Wpath 0 ω‖} := by
      have hmm := (hID_w m).measure_mem_eq (s := {x : Fin (p + 1) → ℝ | c ≤ ‖x‖}) hset
      simpa only [Set.preimage_setOf_eq] using hmm
    rw [hcm, hmid, ← hc0]
  -- The common tail `P{‖u₀‖ ≥ M}` vanishes as `M → ∞` (a.e.-finite random variable).
  have hnorm0 : AEMeasurable (fun ω => ‖e 0 ω • arDesign Y p 0 ω‖) P :=
    (aemeasurable_score h 0).norm
  have hNMS : ∀ M : ℕ,
      NullMeasurableSet {ω | (M : ℝ) ≤ ‖e 0 ω • arDesign Y p 0 ω‖} P := fun M =>
    hnorm0.nullMeasurableSet_preimage measurableSet_Ici
  have hAnti : Antitone
      (fun M : ℕ => {ω | (M : ℝ) ≤ ‖e 0 ω • arDesign Y p 0 ω‖}) := by
    intro M N hMN ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact le_trans (by exact_mod_cast hMN) hω
  have hInt : ⋂ M : ℕ, {ω | (M : ℝ) ≤ ‖e 0 ω • arDesign Y p 0 ω‖} = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_le]
    exact exists_nat_gt ‖e 0 ω • arDesign Y p 0 ω‖
  have htail : Tendsto
      (fun M : ℕ => P {ω | (M : ℝ) ≤ ‖e 0 ω • arDesign Y p 0 ω‖}) atTop (𝓝 0) := by
    have hconv := tendsto_measure_iInter_atTop (μ := P)
      (s := fun M : ℕ => {ω | (M : ℝ) ≤ ‖e 0 ω • arDesign Y p 0 ω‖})
      hNMS hAnti ⟨0, measure_ne_top P _⟩
    rwa [hInt, measure_empty] at hconv
  -- Assemble: one threshold `M₀ + 1` works, uniformly in `n`.
  intro δ hδ
  obtain ⟨M₀, hM₀⟩ := (htail.eventually (Iio_mem_nhds hδ)).exists
  refine ⟨(M₀ : ℝ) + 1, by positivity, Filter.Eventually.of_forall fun n => ?_⟩
  calc P {ω | (M₀ : ℝ) + 1 ≤ ‖e (n : ℤ) ω • arDesign Y p (n : ℤ) ω‖}
      = P {ω | (M₀ : ℝ) + 1 ≤ ‖e 0 ω • arDesign Y p 0 ω‖} := huniform _ (n : ℤ)
    _ ≤ P {ω | (M₀ : ℝ) ≤ ‖e 0 ω • arDesign Y p 0 ω‖} := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        linarith
    _ ≤ δ := le_of_lt hM₀

/-- **Score central limit theorem in plain-vector form (Hansen §14.30).** The normalized score
average `(√n)⁻¹ ∑_{t<n} eₜ xₜ` converges in distribution to the plain-vector view `z ↦ z.ofLp` of
the Gaussian bundle limit. The MDS-CLT bundle `MDSCLTConditionsVec.central_limit` delivers the
analogous statement for the *shifted* partial sums `(√n)⁻¹ ∑_{t<n} u₍ₜ₊₁₎`; the two differ by the
boundary term `(√n)⁻¹(u₀ − uₙ)`, which is asymptotically negligible because the score is bounded in
probability (`score_boundedInProbabilityNorm`, from strict stationarity of `Y`). The Euclidean
bundle limit is transported to plain `Fin (p+1) → ℝ` coordinates through `WithLp.ofLp`. -/
private theorem sampleScore_tendstoInDistribution (h : ARModelConditions Y e ℱ P p coeff)
    (hclt : MDSCLTConditionsVec ℱ (fun t ω => e t ω • arDesign Y p t ω) P)
    (hstat : IsStrictlyStationary Y P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → EuclideanSpace ℝ (Fin (p + 1))}
    (hZ : HasLaw Z (multivariateGaussian 0 hclt.covMat) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ •
        ∑ t ∈ Finset.range n, e (t : ℤ) ω • arDesign Y p (t : ℤ) ω)
      atTop (fun z => (Z z).ofLp) (fun _ => P) P' := by
  classical
  have hc0 : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have humeas : ∀ t : ℤ, AEMeasurable (fun ω => e t ω • arDesign Y p t ω) P := aemeasurable_score h
  have hTmeas : ∀ n : ℕ,
      AEMeasurable (fun ω => (Real.sqrt (n : ℝ))⁻¹ •
        ∑ t ∈ Finset.range n, e (t : ℤ) ω • arDesign Y p (t : ℤ) ω) P := fun n =>
    (Finset.aemeasurable_fun_sum (Finset.range n) fun (t : ℕ) _ =>
      humeas (t : ℤ)).const_smul ((Real.sqrt (n : ℝ))⁻¹)
  -- CLT plain form (over the shifted score `u₍ₜ₊₁₎`).
  have hS : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ •
        ∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω • arDesign Y p ((t : ℤ) + 1) ω)
      atTop (fun z => (Z z).ofLp) (fun _ => P) P' := by
    have hMap := TendstoInDistribution.continuous_comp
      (g := (WithLp.ofLp : EuclideanSpace ℝ (Fin (p + 1)) → (Fin (p + 1) → ℝ)))
      (PiLp.continuous_ofLp 2 (fun _ => ℝ)) (hclt.central_limit hZ)
    simpa [Function.comp_def] using hMap
  -- Boundary corrections vanish in probability.
  have hrem_u0 : TendstoInMeasure P
      (fun (n : ℕ) (_ω : Ω) => (Real.sqrt (n : ℝ))⁻¹ • (e 0 _ω • arDesign Y p 0 _ω))
      atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => ((humeas 0).const_smul ((Real.sqrt (n : ℝ))⁻¹)).aestronglyMeasurable)
      (ae_of_all _ fun ω => by simpa using hc0.smul_const (e 0 ω • arDesign Y p 0 ω))
  have hrem_un : TendstoInMeasure P
      (fun (n : ℕ) ω => (-(Real.sqrt (n : ℝ))⁻¹) • (e (n : ℤ) ω • arDesign Y p (n : ℤ) ω))
      atTop (fun _ => 0) :=
    (score_boundedInProbabilityNorm h hstat).tendstoInMeasure_const_smul_zero
      (by simpa using hc0.neg)
  -- Step 1: `A = S + (√n)⁻¹ u₀`.
  have hA : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ •
          ∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω • arDesign Y p ((t : ℤ) + 1) ω
        + (Real.sqrt (n : ℝ))⁻¹ • (e 0 ω • arDesign Y p 0 ω))
      atTop (fun z => (Z z).ofLp) (fun _ => P) P' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hS ?_ ?_
    · refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hrem_u0
      exact ae_of_all _ fun ω => by simp [Pi.sub_apply]
    · exact fun n =>
        ((Finset.aemeasurable_fun_sum (Finset.range n)
          fun (t : ℕ) _ => humeas ((t : ℤ) + 1)).const_smul ((Real.sqrt (n : ℝ))⁻¹)).add
          ((humeas 0).const_smul ((Real.sqrt (n : ℝ))⁻¹))
  -- Step 2: `T = A − (√n)⁻¹ uₙ`, using `∑ u(t) − ∑ u(t+1) = u₀ − uₙ`.
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hA ?_ hTmeas
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hrem_un
  refine ae_of_all _ fun ω => ?_
  have key : (∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω • arDesign Y p ((t : ℤ) + 1) ω)
        + (e 0 ω • arDesign Y p 0 ω)
      = (∑ t ∈ Finset.range n, e (t : ℤ) ω • arDesign Y p (t : ℤ) ω)
        + (e (n : ℤ) ω • arDesign Y p (n : ℤ) ω) := by
    have h0 : e 0 ω • arDesign Y p 0 ω
        = (fun j : ℕ => e (j : ℤ) ω • arDesign Y p (j : ℤ) ω) 0 := by norm_num
    have hs : (∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω • arDesign Y p ((t : ℤ) + 1) ω)
        = ∑ t ∈ Finset.range n, (fun j : ℕ => e (j : ℤ) ω • arDesign Y p (j : ℤ) ω) (t + 1) :=
      Finset.sum_congr rfl fun t _ => by norm_cast
    rw [h0, hs, ← Finset.sum_range_succ' (fun j : ℕ => e (j : ℤ) ω • arDesign Y p (j : ℤ) ω) n,
      Finset.sum_range_succ (fun j : ℕ => e (j : ℤ) ω • arDesign Y p (j : ℤ) ω) n]
  have hB : (∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω • arDesign Y p ((t : ℤ) + 1) ω)
      = (∑ t ∈ Finset.range n, e (t : ℤ) ω • arDesign Y p (t : ℤ) ω)
        + (e (n : ℤ) ω • arDesign Y p (n : ℤ) ω) - (e 0 ω • arDesign Y p 0 ω) :=
    eq_sub_of_add_eq key
  simp only [Pi.sub_apply, hB]
  module

/-- **Singular-event residual (Hansen §14.30).** The gap between the scaled centered estimator
`√n(α̂ₙ − coeff)` and the Slutsky leading term `Q̂ₙ⁻¹·(√n · score-average)` vanishes in probability.
On the event `{det Q̂ₙ ≠ 0}` the two coincide exactly (score-average bridge `arCrossHat_ae_eq` plus
`Q̂ₙ⁻¹ Q̂ₙ = 1`), so the residual is supported on the singular event `{det Q̂ₙ = 0}`, whose
probability tends to `0` because `Q̂ₙ →ₚ Q` (Theorem 14.29 engine) and `det Q ≠ 0` (Theorem 14.28).
-/
private theorem arLS_residual_tendstoInMeasure_zero (h : ARModelConditions Y e ℱ P p coeff) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (arLSStar Y p n ω - coeff)
        - (arGramHat Y p n ω)⁻¹ *ᵥ ((Real.sqrt (n : ℝ))⁻¹ •
            ∑ t ∈ Finset.range n, e (t : ℤ) ω • arDesign Y p (t : ℤ) ω))
      atTop (fun _ => 0) := by
  have hQ := arGramHat_tendsto h.ergodic h.meas h.memLp p
  have hdetU : IsUnit (arGram Y P p).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h.gram_posDef.isUnit
  have hne : (arGram Y P p).det ≠ 0 := isUnit_iff_ne_zero.mp hdetU
  -- `det Q̂ₙ →ₚ det Q`, hence `P{det Q̂ₙ = 0} → 0`.
  have hdet_tend : TendstoInMeasure P (fun n ω => (arGramHat Y p n ω).det) atTop
      (fun _ => (arGram Y P p).det) :=
    tendstoInMeasure_continuous_comp (fun n => aestronglyMeasurable_arGramHat h.meas p n) hQ
      (Continuous.matrix_det continuous_id)
  have hdet0 : Tendsto (fun n => P {ω | (arGramHat Y p n ω).det = 0}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hdet_tend (ENNReal.ofReal |(arGram Y P p).det|)
        (ENNReal.ofReal_pos.mpr (abs_pos.mpr hne))) (fun _ => zero_le _) (fun n => ?_)
    refine measure_mono (fun ω hω => ?_)
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
  -- `√n · n⁻¹ = (√n)⁻¹`.
  have hsc : ∀ n : ℕ, Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
    intro n
    rcases eq_or_ne (n : ℝ) 0 with hn | hn
    · simp [hn]
    · have hpos : (0 : ℝ) < n := lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)
      have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
      field_simp
      exact Real.sq_sqrt hpos.le
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdet0
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono_ae ?_
  filter_upwards [arCrossHat_ae_eq h n] with ω hbridge hle
  by_contra hdetω
  have hUn : IsUnit (arGramHat Y p n ω).det := isUnit_iff_ne_zero.mpr hdetω
  have hR : Real.sqrt (n : ℝ) • (arLSStar Y p n ω - coeff)
      - (arGramHat Y p n ω)⁻¹ *ᵥ ((Real.sqrt (n : ℝ))⁻¹ •
          ∑ t ∈ Finset.range n, e (t : ℤ) ω • arDesign Y p (t : ℤ) ω) = 0 := by
    rw [arLSStar, hbridge, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hUn, Matrix.one_mulVec, add_sub_cancel_left,
      Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, hsc n, sub_self]
  have hle2 : ε ≤ edist (Real.sqrt (n : ℝ) • (arLSStar Y p n ω - coeff)
      - (arGramHat Y p n ω)⁻¹ *ᵥ ((Real.sqrt (n : ℝ))⁻¹ •
          ∑ t ∈ Finset.range n, e (t : ℤ) ω • arDesign Y p (t : ℤ) ω)) 0 := hle
  rw [hR, edist_self] at hle2
  exact absurd hle2 (not_le.mpr hε)

omit [IsProbabilityMeasure P] in
/-- A.e.-strong measurability of the least-squares estimator `α̂ₙ = Q̂ₙ⁻¹ ĉₙ`. -/
private theorem aestronglyMeasurable_arLSStar (h : ARModelConditions Y e ℱ P p coeff) (n : ℕ) :
    AEStronglyMeasurable (fun ω => arLSStar Y p n ω) P :=
  (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
    ((aestronglyMeasurable_matrix_inv (aestronglyMeasurable_arGramHat h.meas p n)).prodMk
      (aestronglyMeasurable_arCrossHat h.meas p n))

/-- **Hansen Theorem 14.30 (asymptotic normality of the AR(p) least-squares estimator).** Under
correct specification with a martingale-difference innovation (`ARModelConditions`), conditional on
the vector martingale-difference central limit theorem for the score `uₜ = eₜ xₜ` (bundle
`MDSCLTConditionsVec`, Hansen Theorem 14.11) and strict stationarity of `Y` (Hansen's maintained
assumption, which supplies the score `Oₚ(1)` bound via `score_boundedInProbabilityNorm`), the
least-squares estimator is asymptotically normal:
`√n(α̂ₙ − α) ⇒ N(0, Q⁻¹ Σ Q⁻¹)`, where `Q = arGram Y P p` is the design second-moment matrix
(positive definite by Theorem 14.28), `Σ = hclt.covMat` is the score covariance, and
`α = arProjCoeff Y P p = coeff` is the structural coefficient (`arProjCoeff_eq_coeff`).

The limit is phrased in the repository's reference-random-variable idiom, mirroring the Chapter 7
OLS normality theorem `olsBetaStar_vector_tendstoInDistribution_scoreCLT`: it is the image
`ω' ↦ Q⁻¹ ·(Z ω')` of any reference variable `Z` with the Gaussian score law
`multivariateGaussian 0 Σ`. The proof is the Slutsky chain: the score central limit theorem
(`sampleScore_tendstoInDistribution`) supplies `√n · ĝₙ ⇒ Z`, the sample-Gram inverse converges by
the Theorem 14.29 engine (`arGramHat_tendsto`), the random-inverse composition
`matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix` yields `Q̂ₙ⁻¹·√n ĝₙ ⇒ Q⁻¹ Z`, and the
singular-event residual (`arLS_residual_tendstoInMeasure_zero`) closes the gap to `√n(α̂ₙ − α)`. -/
theorem arLS_asymptoticNormal (h : ARModelConditions Y e ℱ P p coeff)
    (hclt : MDSCLTConditionsVec ℱ (fun t ω => e t ω • arDesign Y p t ω) P)
    (hstat : IsStrictlyStationary Y P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → EuclideanSpace ℝ (Fin (p + 1))}
    (hZ : HasLaw Z (multivariateGaussian 0 hclt.covMat) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (arLSStar Y p n ω - arProjCoeff Y P p))
      atTop (fun ω' => (arGram Y P p)⁻¹ *ᵥ (Z ω').ofLp) (fun _ => P) P' := by
  have hdetU : IsUnit (arGram Y P p).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h.gram_posDef.isUnit
  have hcomp := matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix
    (sampleScore_tendstoInDistribution h hclt hstat hZ)
    (fun n => aestronglyMeasurable_arGramHat h.meas p n)
    (arGramHat_tendsto h.ergodic h.meas h.memLp p) hdetU
  rw [arProjCoeff_eq_coeff h]
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hcomp
    (arLS_residual_tendstoInMeasure_zero h) (fun n => ?_)
  exact (((aestronglyMeasurable_arLSStar h n).sub aestronglyMeasurable_const).const_smul
    (Real.sqrt (n : ℝ))).aemeasurable

end AsymptoticNormality

section Homoskedastic

variable {Y e : ℤ → Ω → ℝ} {ℱ : Filtration ℤ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {p : ℕ} {coeff : Fin (p + 1) → ℝ} {σ2 : ℝ}

/-- A real symmetric (Hermitian) matrix is determined by its quadratic form: two Hermitian matrices
with the same quadratic form `a ↦ a ⬝ᵥ (M *ᵥ a)` are equal. The off-diagonal entries are recovered
by polarization at `eᵢ + eⱼ`, the diagonal entries at `eᵢ`. -/
private theorem matrix_ext_of_isHermitian_of_quadratic {k : ℕ}
    {M N : Matrix (Fin k) (Fin k) ℝ} (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hq : ∀ a : Fin k → ℝ, a ⬝ᵥ (M *ᵥ a) = a ⬝ᵥ (N *ᵥ a)) : M = N := by
  have hMsymm : ∀ i j, M j i = M i j := fun i j => by simpa using hM.apply i j
  have hNsymm : ∀ i j, N j i = N i j := fun i j => by simpa using hN.apply i j
  have hdiag : ∀ i, M i i = N i i := fun i => by
    have hi := hq (Pi.single i 1)
    simpa [mulVec_single_one, single_dotProduct, Matrix.col_apply] using hi
  ext i j
  rcases eq_or_ne i j with h | h
  · rw [h]; exact hdiag j
  · have hqij := hq (Pi.single i 1 + Pi.single j 1)
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, mulVec_single_one,
      single_dotProduct, Matrix.col_apply, one_mul] at hqij
    rw [hMsymm i j, hNsymm i j, hdiag i, hdiag j] at hqij
    linarith

/-- Under strict stationarity the design linear form `xₜ ⬝ a` has the same second moment at times
`1` and `0`: `∫ (x₁ ⬝ a)² = ∫ (x₀ ⬝ a)²`. The design linear form is a shift-equivariant functional
of `Y` (`arDesign_eq_path`), so strict stationarity (`comp_shiftEquivariant`, Theorem 14.2) makes
the process `t ↦ xₜ ⬝ a` strictly stationary; its single-time marginals then coincide. -/
private theorem integral_sq_dotProduct_arDesign_shift
    (hstat : IsStrictlyStationary Y P) (hmeas : ∀ t, AEMeasurable (Y t) P)
    (a : Fin (p + 1) → ℝ) :
    ∫ ω, (arDesign Y p 1 ω ⬝ᵥ a) ^ 2 ∂P = ∫ ω, (arDesign Y p 0 ω ⬝ᵥ a) ^ 2 ∂P := by
  have hψ : Measurable (fun y : ℤ → ℝ => arDesignPath p y ⬝ᵥ a) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ => (measurable_arDesignPath_apply p i).mul_const (a i)
  have hstatV : IsStrictlyStationary (fun t ω => arDesign Y p t ω ⬝ᵥ a) P := by
    have heq : (fun t ω => arDesign Y p t ω ⬝ᵥ a)
        = fun t ω => (fun y : ℤ → ℝ => arDesignPath p y ⬝ᵥ a) (fun j => Y (t + j) ω) := by
      funext t ω; rw [arDesign_eq_path]
    rw [heq]
    exact hstat.comp_shiftEquivariant hψ hmeas
  have hID : IdentDistrib (fun ω => arDesign Y p 1 ω ⬝ᵥ a)
      (fun ω => arDesign Y p 0 ω ⬝ᵥ a) P P := by
    have hmem : (0 : ℤ) ∈ ({0} : Finset ℤ) := Finset.mem_singleton.mpr rfl
    have hcomp := (hstatV {0} 1).comp (u := fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩)
      (measurable_pi_apply _)
    have e1 : ((fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩) ∘
        fun ω => ({0} : Finset ℤ).restrict (fun t => arDesign Y p (t + 1) ω ⬝ᵥ a))
        = fun ω => arDesign Y p 1 ω ⬝ᵥ a := by
      funext ω; change arDesign Y p (0 + 1) ω ⬝ᵥ a = _; rw [zero_add]
    have e2 : ((fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩) ∘
        fun ω => ({0} : Finset ℤ).restrict (fun t => arDesign Y p t ω ⬝ᵥ a))
        = fun ω => arDesign Y p 0 ω ⬝ᵥ a := by funext ω; rfl
    rw [e1, e2] at hcomp
    exact hcomp
  exact (hID.comp (measurable_id.pow_const 2)).integral_eq

/-- **Homoskedastic covariance identification (Hansen §14.31), quadratic-form version.** Under
conditional homoskedasticity `𝔼[eₜ² | ℱₜ₋₁] = σ²` and strict stationarity, the score covariance
matrix `Σ = hclt.covMat` satisfies `a' Σ a = σ² · a' Q a` for every direction `a`, where
`Q = arGram Y P p`. The chain: `variance_proj` writes `a'Σa` as the second moment of the projected
score `u₁ ⬝ a = e₁ (x₁ ⬝ a)` (mean zero by the score MDS property); the conditional-homoskedasticity
pull-out (the `ℱ₀`-measurable factor `(x₁ ⬝ a)²` times `𝔼[e₁² | ℱ₀] = σ²`) extracts `σ²`; and strict
stationarity moves the anchor from time `1` to time `0`, giving `σ² · a' Q a`. -/
private theorem covMat_quadForm_eq_smul (h : ARModelConditions Y e ℱ P p coeff)
    (hclt : MDSCLTConditionsVec ℱ (fun t ω => e t ω • arDesign Y p t ω) P)
    (hstat : IsStrictlyStationary Y P)
    (hhom : ∀ t, P[fun ω => (e t ω) ^ 2 | ℱ (t - 1)] =ᵐ[P] fun _ => σ2)
    (a : Fin (p + 1) → ℝ) :
    a ⬝ᵥ (hclt.covMat *ᵥ a) = σ2 * (a ⬝ᵥ (arGram Y P p *ᵥ a)) := by
  have hmean : ∫ ω, (e 1 ω • arDesign Y p 1 ω) ⬝ᵥ a ∂P = 0 :=
    (scoreIsMDS h a).integral_eq_zero 1
  have haem : AEMeasurable (fun ω => (e 1 ω • arDesign Y p 1 ω) ⬝ᵥ a) P :=
    ((scoreIsMDS h a).integrable 1).aemeasurable
  have hvar : a ⬝ᵥ (hclt.covMat *ᵥ a)
      = ∫ ω, ((e 1 ω • arDesign Y p 1 ω) ⬝ᵥ a) ^ 2 ∂P := by
    rw [← hclt.variance_proj a, variance_of_integral_eq_zero haem hmean]
  have hint_e2 : Integrable (fun ω => (e 1 ω) ^ 2) P :=
    ((memLp_e (h.recursion 1) h.memLp).integrable_mul
      (memLp_e (h.recursion 1) h.memLp)).congr
      (Filter.Eventually.of_forall fun ω => (pow_two (e 1 ω)).symm)
  have hint_gX : Integrable (fun ω => (arDesign Y p 1 ω ⬝ᵥ a) ^ 2 * (e 1 ω) ^ 2) P := by
    refine (((hclt.proj a).memLp_two 1).integrable_mul ((hclt.proj a).memLp_two 1)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply, smul_dotProduct, smul_eq_mul]; ring
  have hg_sm : StronglyMeasurable[ℱ 0] (fun ω => (arDesign Y p 1 ω ⬝ᵥ a) ^ 2) := by
    have hsm := stronglyMeasurable_dotProduct_arDesign h.adapted p 1 a
    rw [show (1 : ℤ) - 1 = 0 from by ring] at hsm
    exact hsm.pow 2
  have hhom1 : P[fun ω => (e 1 ω) ^ 2 | ℱ 0] =ᵐ[P] fun _ => σ2 := by
    have h1 := hhom 1; rwa [show (1 : ℤ) - 1 = 0 from by ring] at h1
  have hpull : ∫ ω, (arDesign Y p 1 ω ⬝ᵥ a) ^ 2 * (e 1 ω) ^ 2 ∂P
      = σ2 * ∫ ω, (arDesign Y p 1 ω ⬝ᵥ a) ^ 2 ∂P := by
    have hfg : (fun ω => (arDesign Y p 1 ω ⬝ᵥ a) ^ 2 * (e 1 ω) ^ 2)
        = (fun ω => (arDesign Y p 1 ω ⬝ᵥ a) ^ 2) * fun ω => (e 1 ω) ^ 2 := rfl
    have key : ∫ ω, (arDesign Y p 1 ω ⬝ᵥ a) ^ 2 * (e 1 ω) ^ 2 ∂P
        = ∫ ω, (arDesign Y p 1 ω ⬝ᵥ a) ^ 2 * σ2 ∂P := by
      rw [hfg, ← integral_condExp (ℱ.le 0),
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hg_sm (hfg ▸ hint_gX) hint_e2)]
      refine integral_congr_ae ?_
      filter_upwards [hhom1] with ω hh
      simp only [Pi.mul_apply, hh]
    rw [key, integral_mul_const, mul_comm]
  have hcomm : (fun ω => (arDesign Y p 0 ω ⬝ᵥ a) ^ 2)
      = fun ω => (a ⬝ᵥ arDesign Y p 0 ω) ^ 2 := funext fun ω => by rw [dotProduct_comm]
  rw [hvar, show (fun ω => ((e 1 ω • arDesign Y p 1 ω) ⬝ᵥ a) ^ 2)
      = fun ω => (arDesign Y p 1 ω ⬝ᵥ a) ^ 2 * (e 1 ω) ^ 2 from
    funext fun ω => by simp only [smul_dotProduct, smul_eq_mul]; ring,
    hpull, integral_sq_dotProduct_arDesign_shift hstat h.meas a, hcomm,
    dotProduct_arGram_mulVec h.memLp p a]

/-- **Homoskedastic covariance identification (Hansen §14.31).** Under conditional homoskedasticity
and strict stationarity the score covariance matrix collapses to a scalar multiple of the design
Gram: `Σ = σ² Q`. Both matrices are symmetric (`posSemidef.isHermitian`, `arGram_isHermitian`), so
they are determined by their quadratic forms, which agree by `covMat_quadForm_eq_smul`. -/
private theorem covMat_eq_smul_arGram (h : ARModelConditions Y e ℱ P p coeff)
    (hclt : MDSCLTConditionsVec ℱ (fun t ω => e t ω • arDesign Y p t ω) P)
    (hstat : IsStrictlyStationary Y P)
    (hhom : ∀ t, P[fun ω => (e t ω) ^ 2 | ℱ (t - 1)] =ᵐ[P] fun _ => σ2) :
    hclt.covMat = σ2 • arGram Y P p := by
  refine matrix_ext_of_isHermitian_of_quadratic hclt.posSemidef.isHermitian
    ((arGram_isHermitian p).smul (show IsSelfAdjoint σ2 from star_trivial σ2)) (fun a => ?_)
  rw [covMat_quadForm_eq_smul h hclt hstat hhom a, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

/-- **Hansen Theorem 14.31 (asymptotic normality under conditional homoskedasticity).** The
homoskedastic specialization of Theorem 14.30: when `𝔼[eₜ² | ℱₜ₋₁] = σ²` and `Y` is strictly
stationary, the score covariance is `σ² Q` (`covMat_eq_smul_arGram`), so `√n(α̂ₙ − α)` is
asymptotically normal with sandwich covariance `Q⁻¹(σ² Q)Q⁻¹ = σ² Q⁻¹` — expressed here, as in
Theorem 14.30, through the reference variable `Z` carrying the Gaussian law
`multivariateGaussian 0 (σ² Q)`. -/
theorem arLS_asymptoticNormal_homoskedastic (h : ARModelConditions Y e ℱ P p coeff)
    (hclt : MDSCLTConditionsVec ℱ (fun t ω => e t ω • arDesign Y p t ω) P)
    (hstat : IsStrictlyStationary Y P)
    (hhom : ∀ t, P[fun ω => (e t ω) ^ 2 | ℱ (t - 1)] =ᵐ[P] fun _ => σ2)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → EuclideanSpace ℝ (Fin (p + 1))}
    (hZ : HasLaw Z (multivariateGaussian 0 (σ2 • arGram Y P p)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (arLSStar Y p n ω - arProjCoeff Y P p))
      atTop (fun ω' => (arGram Y P p)⁻¹ *ᵥ (Z ω').ofLp) (fun _ => P) P' := by
  rw [← covMat_eq_smul_arGram h hclt hstat hhom] at hZ
  exact arLS_asymptoticNormal h hclt hstat hZ

end Homoskedastic

/-! ### Theorem 14.32: asymptotic normality of the AR(p) least-squares estimator under mixing

Hansen **Theorem 14.32** drops the martingale-difference assumption on the innovation: `Y` is a
strictly stationary, ergodic, `Lʳ`-integrable (`r > 4`) α-mixing process, and the AR(p) fit is the
best linear predictor (projection) `α = arProjCoeff Y P p`. The projection error `eₜ = Yₜ − xₜ ⬝ α`
is generally *not* an MDS, so the score `wₜ = eₜ xₜ` has autocorrelation and the relevant central
limit theorem is the α-mixing CLT (Hansen 14.15), delivering the sandwich covariance
`Q⁻¹ Ω Q⁻¹` with `Ω` the score's long-run covariance matrix.

The **unconditional** deliverable here is `summable_autocov_scoreProj_of_mixing`: every linear
projection `a ⬝ wₜ = eₜ (xₜ ⬝ a)` of the score has absolutely summable autocovariances, so its
long-run variance `Ω(a) = ∑_{ℓ∈ℤ} γ_{a⬝w}(ℓ)` is well defined (hence the long-run covariance matrix
exists). This is the mixing analogue of the well-definedness that underlies Hansen's Ω. The
mechanism is Hansen Theorem 14.12 (`mixingCoeff_comp_le`): `a ⬝ wₜ` is a `(p+1)`-lag measurable
transformation of `Y`, so its mixing coefficients are dominated by those of `Y` shifted by `p`, and
`summable_autocov_of_mixing` (the Davydov bound, Hansen 14.13.2) then gives summability with the
matching exponent `1 − 2/(r/2) = 1 − 4/r` on the `Lʳ/²` score projection. -/

section MixingNormality

open HansenEconometrics

variable {Y : ℤ → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {p : ℕ}

/-- **Standing hypotheses for Hansen Theorem 14.32 (AR(p) normality under general dependence).** The
observed process `Y` is strictly stationary, ergodic, and `Lʳ`-integrable for some `r > 4`, its
strong-mixing coefficients satisfy `∑ α(ℓ)^{1−4/r} < ∞`, and the population design Gram
`Q = arGram Y P p` is positive definite (Hansen's identification condition, Theorem 14.28). Unlike
`ARModelConditions`, the innovation is *not* assumed to be a martingale difference sequence: the
AR(p) fit is the best linear predictor `α = arProjCoeff Y P p`, so the projection error is only
required to be uncorrelated with the regressors, which the normal equations supply automatically. -/
structure ARMixingConditions (Y : ℤ → Ω → ℝ) (P : Measure Ω) (p : ℕ) (r : ℝ) : Prop where
  /-- `Y` is strictly stationary. -/
  stationary : IsStrictlyStationary Y P
  /-- `Y` is ergodic (consumed by the ergodic LLN giving `Q̂ₙ →ₚ Q`). -/
  ergodic : IsErgodicProcess Y P
  /-- Each coordinate of `Y` is measurable (needed by the mixing machinery). -/
  meas : ∀ t, Measurable (Y t)
  /-- The moment exponent exceeds `4` (Hansen's `E|Y|^r < ∞`, `r > 4`). -/
  hr : 4 < r
  /-- The marginal `Y₀` is `Lʳ`-integrable. -/
  memLp : MemLp (Y 0) (ENNReal.ofReal r) P
  /-- The strong-mixing coefficients satisfy `∑ α(ℓ)^{1−4/r} < ∞`. -/
  summable_mixing : Summable (fun ℓ : ℕ => mixingCoeff Y P ℓ ^ (1 - 4 / r))
  /-- **Identification (Theorem 14.28).** The population design Gram `Q = arGram Y P p` is positive
  definite. -/
  gram_posDef : (arGram Y P p).PosDef

/-- Measurability of a single design coordinate at time `t`. -/
private theorem measurable_arDesign_apply (hmeas : ∀ t, Measurable (Y t)) (t : ℤ)
    (i : Fin (p + 1)) :
    Measurable (fun ω => arDesign Y p t ω i) := by
  by_cases h : i = 0
  · simp only [arDesign, if_pos h]; exact measurable_const
  · simp only [arDesign, if_neg h]; exact hmeas _

/-- Measurability of a design linear form `xₜ ⬝ c`. -/
private theorem measurable_arDesign_dotProduct (hmeas : ∀ t, Measurable (Y t)) (t : ℤ)
    (c : Fin (p + 1) → ℝ) : Measurable (fun ω => arDesign Y p t ω ⬝ᵥ c) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ => (measurable_arDesign_apply hmeas t i).mul_const (c i)

omit [IsProbabilityMeasure P] in
/-- Single-coordinate identical distribution from strict stationarity: `Y s ≟ Y 0`. -/
private theorem identDistrib_arCoord (hSS : IsStrictlyStationary Y P) (s : ℤ) :
    IdentDistrib (Y s) (Y 0) P P := by
  have hmem : (0 : ℤ) ∈ ({0} : Finset ℤ) := Finset.mem_singleton.mpr rfl
  have hcomp := (hSS {0} s).comp (u := fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩)
    (measurable_pi_apply _)
  have e1 : ((fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩) ∘
      fun ω => ({0} : Finset ℤ).restrict (fun t => Y (t + s) ω)) = Y s := by
    funext ω; change Y (0 + s) ω = Y s ω; rw [zero_add]
  have e2 : ((fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩) ∘
      fun ω => ({0} : Finset ℤ).restrict (fun t => Y t ω)) = Y 0 := by
    funext ω; rfl
  rw [e1, e2] at hcomp
  exact hcomp

/-- Each design coordinate at time `0` lies in `Lʳ`: the intercept is a constant and each lag
`Y_{−i}` is identically distributed to `Y₀ ∈ Lʳ`. -/
private theorem memLp_arDesign_coord_ofReal (hSS : IsStrictlyStationary Y P) {r : ℝ}
    (hmem : MemLp (Y 0) (ENNReal.ofReal r) P) (i : Fin (p + 1)) :
    MemLp (fun ω => arDesign Y p 0 ω i) (ENNReal.ofReal r) P := by
  by_cases h : i = 0
  · simp only [arDesign, if_pos h]; exact memLp_const 1
  · have hid : MemLp (Y (0 - (i.val : ℤ))) (ENNReal.ofReal r) P :=
      (identDistrib_arCoord hSS (0 - (i.val : ℤ))).memLp_iff.mpr hmem
    have hEq : (fun ω => arDesign Y p 0 ω i) = Y (0 - (i.val : ℤ)) := by
      funext ω; simp only [arDesign, if_neg h]
    rw [hEq]; exact hid

/-- The design linear form `x₀ ⬝ c` lies in `Lʳ` (a finite sum of `Lʳ` coordinates). -/
private theorem memLp_arDesign_dotProduct_ofReal (hSS : IsStrictlyStationary Y P) {r : ℝ}
    (hmem : MemLp (Y 0) (ENNReal.ofReal r) P) (c : Fin (p + 1) → ℝ) :
    MemLp (fun ω => arDesign Y p 0 ω ⬝ᵥ c) (ENNReal.ofReal r) P := by
  have hrw : (fun ω => arDesign Y p 0 ω ⬝ᵥ c) = ∑ i, fun ω => arDesign Y p 0 ω i * c i := by
    funext ω; simp only [Finset.sum_apply, dotProduct]
  rw [hrw]
  exact memLp_finset_sum' _ fun i _ => (memLp_arDesign_coord_ofReal hSS hmem i).mul_const (c i)

/-- The backward design window `(1, w₁, …, w_p)` of a coordinate tuple `w : Fin (p+1) → ℝ`.
Composing with the backward history `w = (Y_t, Y_{t−1}, …, Y_{t−p})` recovers the AR(p) design at
time `t`. -/
private def windowDesign (p : ℕ) (w : Fin (p + 1) → ℝ) : Fin (p + 1) → ℝ :=
  fun i => if i = 0 then 1 else w i

/-- The projected score written as a finite-lag functional of the backward window
`w = (y_t, y_{t−1}, …, y_{t−p})`: `(y_t − x ⬝ α)(x ⬝ a)` with `x = windowDesign p w`. -/
private def scoreWindow (p : ℕ) (α a w : Fin (p + 1) → ℝ) : ℝ :=
  (w 0 - windowDesign p w ⬝ᵥ α) * (windowDesign p w ⬝ᵥ a)

private theorem measurable_windowDesign_apply (p : ℕ) (i : Fin (p + 1)) :
    Measurable (fun w : Fin (p + 1) → ℝ => windowDesign p w i) := by
  by_cases h : i = 0
  · simp only [windowDesign, if_pos h]; exact measurable_const
  · simp only [windowDesign, if_neg h]; exact measurable_pi_apply _

private theorem measurable_scoreWindow (p : ℕ) (α a : Fin (p + 1) → ℝ) :
    Measurable (scoreWindow p α a) := by
  refine ((measurable_pi_apply 0).sub ?_).mul ?_
  · simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ => (measurable_windowDesign_apply p i).mul_const (α i)
  · simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ => (measurable_windowDesign_apply p i).mul_const (a i)

omit [MeasurableSpace Ω] in
/-- The backward window of `Y` at time `t` reconstructs the AR(p) design: `windowDesign` applied to
`(Y_t, Y_{t−1}, …, Y_{t−p})` is `arDesign Y p t`. -/
private theorem windowDesign_arWindow (t : ℤ) (ω : Ω) :
    windowDesign p (fun j : Fin (p + 1) => Y (t - (j : ℤ)) ω) = arDesign Y p t ω := by
  funext i
  simp only [windowDesign, arDesign]

omit [MeasurableSpace Ω] in
/-- The projected score `a ⬝ wₜ = eₜ (xₜ ⬝ a)` is the finite-lag functional `scoreWindow` of the
backward window of `Y`. This is the identity that exhibits the score as a `(p+1)`-lag transformation
of `Y`, feeding Hansen Theorem 14.12. -/
private theorem scoreProj_eq_scoreWindow (α a : Fin (p + 1) → ℝ) (t : ℤ) (ω : Ω) :
    (Y t ω - arDesign Y p t ω ⬝ᵥ α) * (arDesign Y p t ω ⬝ᵥ a)
      = scoreWindow p α a (fun j : Fin (p + 1) => Y (t - (j : ℤ)) ω) := by
  have hw0 : (fun j : Fin (p + 1) => Y (t - (j : ℤ)) ω) 0 = Y t ω := by
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
  simp only [scoreWindow, windowDesign_arWindow, hw0]

/-- **Hansen Theorem 14.32 (well-definedness of the long-run score covariance).** Under
`ARMixingConditions`, every linear projection `a ⬝ wₜ = eₜ (xₜ ⬝ a)` of the AR(p) score
`wₜ = eₜ xₜ` (`eₜ = Yₜ − xₜ ⬝ arProjCoeff Y P p` the projection error) has absolutely summable
autocovariances. Consequently its long-run variance `Ω(a) = ∑_{ℓ∈ℤ} γ_{a⬝w}(ℓ)` is well defined, so
the score's long-run covariance matrix (whose quadratic form is `a ↦ Ω(a)`) exists — the mixing
analogue of the score covariance underlying Theorems 14.30/14.32.

This is the **unconditional** core of Theorem 14.32. The projected score is a `(p+1)`-lag measurable
transformation of `Y`, so Hansen Theorem 14.12 (`mixingCoeff_comp_le`) dominates its mixing
coefficients (beyond lag `p`) by those of `Y`, and the Davydov bound (Hansen Theorem 14.13.2, via
`summable_autocov_of_mixing`) gives summability at the `Lʳ/²` moment level with the matching
exponent `1 − 2/(r/2) = 1 − 4/r`. -/
theorem summable_autocov_scoreProj_of_mixing {r : ℝ} (h : ARMixingConditions Y P p r)
    (a : Fin (p + 1) → ℝ) :
    Summable (fun ℓ : ℕ => |autocov
      (fun t ω => (Y t ω - arDesign Y p t ω ⬝ᵥ arProjCoeff Y P p)
        * (arDesign Y p t ω ⬝ᵥ a)) P (ℓ : ℤ)|) := by
  set α := arProjCoeff Y P p with hα
  set S : ℤ → Ω → ℝ := fun t ω => (Y t ω - arDesign Y p t ω ⬝ᵥ α) * (arDesign Y p t ω ⬝ᵥ a)
    with hS
  have hr0 : (0 : ℝ) < r := by linarith [h.hr]
  have hr2 : (2 : ℝ) < r / 2 := by linarith [h.hr]
  -- `S` is the forward shift-equivariant functional `Ψ` of the `Y`-path.
  set Ψ : (ℤ → ℝ) → ℝ :=
    fun y => (y 0 - arDesignPath p y ⬝ᵥ α) * (arDesignPath p y ⬝ᵥ a) with hΨ
  have hΨmeas : Measurable Ψ := by
    refine ((measurable_pi_apply 0).sub ?_).mul ?_
    · simp only [dotProduct]
      exact Finset.measurable_sum _ fun i _ => (measurable_arDesignPath_apply p i).mul_const (α i)
    · simp only [dotProduct]
      exact Finset.measurable_sum _ fun i _ => (measurable_arDesignPath_apply p i).mul_const (a i)
  have hSΨ : S = fun t ω => Ψ (fun l => Y (t + l) ω) := by
    funext t ω
    simp only [hS, hΨ, ← arDesign_eq_path Y p t ω, add_zero]
  -- Measurability of `S`.
  have hSmeas : ∀ t, Measurable (S t) := by
    intro t
    rw [hSΨ]
    exact hΨmeas.comp (measurable_pi_iff.mpr fun l => h.meas (t + l))
  -- Strict stationarity of `S` via `comp_shiftEquivariant`.
  have hSstat : IsStrictlyStationary S P := by
    rw [hSΨ]
    exact h.stationary.comp_shiftEquivariant hΨmeas (fun t => (h.meas t).aemeasurable)
  -- `L^{r/2}` integrability of `S 0` by Hölder (product of two `Lʳ` factors).
  have hmemLp : MemLp (S 0) (ENNReal.ofReal (r / 2)) P := by
    have hf1 : MemLp (fun ω => Y 0 ω - arDesign Y p 0 ω ⬝ᵥ α) (ENNReal.ofReal r) P :=
      h.memLp.sub (memLp_arDesign_dotProduct_ofReal h.stationary h.memLp α)
    have hf2 : MemLp (fun ω => arDesign Y p 0 ω ⬝ᵥ a) (ENNReal.ofReal r) P :=
      memLp_arDesign_dotProduct_ofReal h.stationary h.memLp a
    haveI hHolder : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal r)
        (ENNReal.ofReal (r / 2)) := by
      refine ⟨?_⟩
      rw [← ENNReal.ofReal_inv_of_pos hr0,
        ← ENNReal.ofReal_inv_of_pos (by linarith : (0:ℝ) < r / 2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    change MemLp (fun ω => (Y 0 ω - arDesign Y p 0 ω ⬝ᵥ α) * (arDesign Y p 0 ω ⬝ᵥ a))
      (ENNReal.ofReal (r / 2)) P
    exact hf2.mul' hf1
  -- Mixing summability of `S` from Theorem 14.12 on the tail.
  have hSback : S = fun t ω => scoreWindow p α a (fun j : Fin (p + 1) => Y (t - (j : ℤ)) ω) := by
    funext t ω; exact scoreProj_eq_scoreWindow α a t ω
  have hmixbound : ∀ ℓ : ℕ, p ≤ ℓ → mixingCoeff S P ℓ ≤ mixingCoeff Y P (ℓ - p) := by
    intro ℓ hℓ
    rw [hSback]
    exact mixingCoeff_comp_le (measurable_scoreWindow p α a) Y hℓ
  have hmix : Summable (fun ℓ : ℕ => mixingCoeff S P ℓ ^ (1 - 2 / (r / 2))) := by
    have hexp : (1 : ℝ) - 2 / (r / 2) = 1 - 4 / r := by field_simp; ring
    simp only [hexp]
    have hnn : (0 : ℝ) ≤ 1 - 4 / r := by
      rw [sub_nonneg, div_le_one hr0]; linarith [h.hr]
    have hshift : Summable (fun ℓ : ℕ => mixingCoeff S P (ℓ + p) ^ (1 - 4 / r)) := by
      refine Summable.of_nonneg_of_le
        (fun ℓ => Real.rpow_nonneg (mixingCoeff_nonneg S P (ℓ + p)) _) (fun ℓ => ?_)
        h.summable_mixing
      have hb : mixingCoeff S P (ℓ + p) ≤ mixingCoeff Y P ℓ := by
        have := hmixbound (ℓ + p) (Nat.le_add_left p ℓ)
        rwa [Nat.add_sub_cancel] at this
      exact Real.rpow_le_rpow (mixingCoeff_nonneg S P (ℓ + p)) hb hnn
    exact (summable_nat_add_iff p).mp hshift
  exact summable_autocov_of_mixing hSmeas hSstat hr2 hmemLp hmix

/-! ### The vector α-mixing CLT bundle

The vector analogue of `MixingCLTConditions`, carrying one scalar mixing-CLT bundle per projection
direction together with an explicit long-run covariance matrix, exactly mirroring
`MDSCLTConditionsVec` over the scalar `MDSCLTConditions`. Its endpoint `central_limit` is the
Cramér–Wold assembly of the projected scalar mixing CLTs (Hansen 14.15), and it is the input the
mixing-case normality theorems 14.32 and 14.35(c) consume. -/

/-- **Hansen Theorem 14.15 hypotheses, multivariate form (assumption bundle).** For a
`(ι → ℝ)`-valued process `u`, one scalar `MixingCLTConditions` per linear projection `a ⬝ u`
(the projectionwise analytic core), plus the explicit long-run covariance matrix `Ω = covMat`,
its positive semidefiniteness, and the projected-long-run-variance identity
`Ω(a) = longRunVariance (a ⬝ u) = a' Ω a`. This is the mixing analogue of `MDSCLTConditionsVec`,
with `longRunVariance` replacing the martingale-difference bundle's `variance`. -/
structure MixingCLTConditionsVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ℤ → Ω → (ι → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- Every scalar projection `a ⬝ u` satisfies the scalar Theorem 14.15 hypothesis bundle. -/
  proj : ∀ a : ι → ℝ, MixingCLTConditions (fun t ω => u t ω ⬝ᵥ a) P
  /-- The long-run covariance matrix `Ω`. -/
  covMat : Matrix ι ι ℝ
  /-- `Ω` is positive semidefinite (as a genuine limiting covariance matrix). -/
  posSemidef : covMat.PosSemidef
  /-- `Ω` is tied to the projected long-run variances: `longRunVariance (a ⬝ u) = a' Ω a`. -/
  variance_proj : ∀ a : ι → ℝ,
    longRunVariance (fun t ω => u t ω ⬝ᵥ a) P = a ⬝ᵥ (covMat *ᵥ a)

/-- Coordinatewise measurability of a vector process carrying a `MixingCLTConditionsVec` bundle,
recovered from the projection along the `i`-th standard basis vector. -/
private theorem MixingCLTConditionsVec.aemeasurable_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ℤ → Ω → (ι → ℝ)} (h : MixingCLTConditionsVec u P) (t : ℤ) (i : ι) :
    AEMeasurable (fun ω => u t ω i) P := by
  have hmeas : AEMeasurable (fun ω => u t ω ⬝ᵥ Pi.single i (1 : ℝ)) P :=
    ((h.proj (Pi.single i 1)).measurable t).aemeasurable
  refine hmeas.congr (ae_of_all _ fun ω => ?_)
  simp only [dotProduct_single, mul_one]

/-- **Hansen Theorem 14.15 — multivariate α-mixing central limit theorem (bundle endpoint).** From
the vector bundle `MixingCLTConditionsVec`, the normalized vector partial sums
`(√n)⁻¹ • ∑_{t < n} u₍ₜ₊₁₎` converge in distribution to a `N(0, Ω)` limit on `EuclideanSpace ℝ ι`,
against any reference variable `Z` with `HasLaw Z (multivariateGaussian 0 Ω) P'`. The proof is the
Cramér–Wold reduction: for each direction `a = t.ofLp`, the projected process `a ⬝ u` is a scalar
bundle (`h.proj a`) whose `MixingCLTConditions.central_limit` delivers the scalar CLT, with limit
`gaussianReal 0 (longRunVariance (a ⬝ u)).toNNReal = gaussianReal 0 (a' Ω a).toNNReal`, matching the
projection of `multivariateGaussian 0 Ω`; the projectionwise limits are assembled by
`cramerWold_tendstoInDistribution`. It mirrors `MDSCLTConditionsVec.central_limit` line for line,
with `longRunVariance` replacing `variance`. -/
theorem MixingCLTConditionsVec.central_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ℤ → Ω → (ι → ℝ)} {Ω' : Type*} {m' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → EuclideanSpace ℝ ι}
    (h : MixingCLTConditionsVec u P)
    (hZ : HasLaw Z (multivariateGaussian 0 h.covMat) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω))
      Filter.atTop Z (fun _ => P) P' := by
  refine HansenEconometrics.cramerWold_tendstoInDistribution ?_ hZ.aemeasurable ?_
  · intro n
    refine (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable.comp_aemeasurable ?_
    refine aemeasurable_pi_iff.2 fun i => ?_
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact (Finset.aemeasurable_fun_sum _ fun (s : ℕ) _ =>
      h.aemeasurable_apply ((s : ℤ) + 1) i).const_mul _
  · intro t
    let a : ι → ℝ := t.ofLp
    have hgp : HasLaw
        (fun z : EuclideanSpace ℝ ι => (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) t) z)
        (gaussianReal 0 (longRunVariance (fun t ω => u t ω ⬝ᵥ a) P).toNNReal)
        (multivariateGaussian 0 h.covMat) := by
      rw [h.variance_proj a]
      refine (HansenEconometrics.hasLaw_multivariateGaussian_zero_dotProduct
        h.posSemidef a).congr (ae_of_all _ fun z => ?_)
      change inner ℝ t z = z.ofLp ⬝ᵥ a
      simpa [a] using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := ι) t.ofLp z.ofLp)
    have hscalar := (h.proj a).central_limit (hgp.fun_comp hZ)
    refine TendstoInDistribution.congr (fun n => ?_) Filter.EventuallyEq.rfl hscalar
    refine ae_of_all P fun ω => ?_
    have hV : inner ℝ t
          (WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ • ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω))
        = ((Real.sqrt (n : ℝ))⁻¹ • ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω) ⬝ᵥ a := by
      have hinner := EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := ι) a
        ((Real.sqrt (n : ℝ))⁻¹ • ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω)
      rw [star_trivial] at hinner
      exact hinner
    change (Real.sqrt (n : ℝ))⁻¹ * ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω ⬝ᵥ a
      = inner ℝ t
          (WithLp.toLp 2 ((Real.sqrt (n : ℝ))⁻¹ • ∑ s ∈ Finset.range n, u ((s : ℤ) + 1) ω))
    rw [hV, smul_dotProduct, smul_eq_mul, sum_dotProduct]

/-! ### Shared assembly engines for the mixing/MDS normality endpoints

Three generic private engines factor the Slutsky assembly shared by Theorems 14.32 and
14.35(b)(c) (Theorem 14.30 keeps its own bespoke versions; these are additive):
`boundedInProbabilityNorm_shiftEquivariant` (score tightness from strict stationarity),
`sampleSum_unshift_tendstoInDistribution` (the `∑ u₍ₜ₊₁₎ → ∑ uₜ` boundary correction, agnostic to
whether the shifted-sum CLT comes from the MDS or the mixing bundle), and
`leastSquares_asymptoticNormal_of_scoreCLT` (the random-inverse Slutsky composition plus the
singular-event residual, over an abstract sample Gram/cross-moment/score triple). -/

/-- **Score tightness from strict stationarity (shared engine).** Any process obtained by applying a
fixed measurable functional `W` to the shifted history of a strictly stationary process `X` is
bounded in probability (`Oₚ(1)`): its single-time marginals all coincide with the one at time `0`
(strict stationarity via `comp_shiftEquivariant`, Theorem 14.2), whose norm tail `P{‖·‖ ≥ M}`
vanishes as `M → ∞`. This is the generic form of `score_boundedInProbabilityNorm`, discharging the
`(√n)⁻¹ uₙ` boundary term in every score central limit theorem. -/
private theorem boundedInProbabilityNorm_shiftEquivariant
    {E : Type*} [MeasurableSpace E] {ι : Type*} [Fintype ι]
    {X : ℤ → Ω → E} (hstat : IsStrictlyStationary X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    {W : (ℤ → E) → (ι → ℝ)} (hW : Measurable W) :
    BoundedInProbabilityNorm P (fun n ω => W (fun l => X ((n : ℤ) + l) ω)) := by
  classical
  set Wproc : ℤ → Ω → (ι → ℝ) := fun t ω => W (fun l => X (t + l) ω) with hWproc
  have hstatW : IsStrictlyStationary Wproc P := hstat.comp_shiftEquivariant hW hmeas
  have hID : ∀ m : ℤ, IdentDistrib (Wproc m) (Wproc 0) P P := by
    intro m
    have hmem : (0 : ℤ) ∈ ({0} : Finset ℤ) := Finset.mem_singleton.mpr rfl
    have hcomp := (hstatW {0} m).comp
      (u := fun f : ({0} : Finset ℤ) → (ι → ℝ) => f ⟨0, hmem⟩) (measurable_pi_apply _)
    have e1 : ((fun f : ({0} : Finset ℤ) → (ι → ℝ) => f ⟨0, hmem⟩) ∘
        fun ω => ({0} : Finset ℤ).restrict (fun t => Wproc (t + m) ω)) = Wproc m := by
      funext ω; change Wproc (0 + m) ω = Wproc m ω; rw [zero_add]
    have e2 : ((fun f : ({0} : Finset ℤ) → (ι → ℝ) => f ⟨0, hmem⟩) ∘
        fun ω => ({0} : Finset ℤ).restrict (fun t => Wproc t ω)) = Wproc 0 := by
      funext ω; rfl
    rw [e1, e2] at hcomp
    exact hcomp
  have huniform : ∀ (c : ℝ) (m : ℤ),
      P {ω | c ≤ ‖Wproc m ω‖} = P {ω | c ≤ ‖Wproc 0 ω‖} := by
    intro c m
    have hset : MeasurableSet {x : ι → ℝ | c ≤ ‖x‖} :=
      measurableSet_le measurable_const measurable_norm
    have hmm := (hID m).measure_mem_eq (s := {x : ι → ℝ | c ≤ ‖x‖}) hset
    simpa only [Set.preimage_setOf_eq] using hmm
  have hnorm0 : AEMeasurable (fun ω => ‖Wproc 0 ω‖) P :=
    (hW.comp_aemeasurable (aemeasurable_pi_iff.mpr fun l => hmeas (0 + l))).norm
  have hNMS : ∀ M : ℕ, NullMeasurableSet {ω | (M : ℝ) ≤ ‖Wproc 0 ω‖} P := fun M =>
    hnorm0.nullMeasurableSet_preimage measurableSet_Ici
  have hAnti : Antitone (fun M : ℕ => {ω | (M : ℝ) ≤ ‖Wproc 0 ω‖}) := by
    intro M N hMN ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact le_trans (by exact_mod_cast hMN) hω
  have hInt : ⋂ M : ℕ, {ω | (M : ℝ) ≤ ‖Wproc 0 ω‖} = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_forall, not_le]
    exact exists_nat_gt ‖Wproc 0 ω‖
  have htail : Tendsto (fun M : ℕ => P {ω | (M : ℝ) ≤ ‖Wproc 0 ω‖}) atTop (𝓝 0) := by
    have hconv := tendsto_measure_iInter_atTop (μ := P)
      (s := fun M : ℕ => {ω | (M : ℝ) ≤ ‖Wproc 0 ω‖}) hNMS hAnti ⟨0, measure_ne_top P _⟩
    rwa [hInt, measure_empty] at hconv
  intro δ hδ
  obtain ⟨M₀, hM₀⟩ := (htail.eventually (Iio_mem_nhds hδ)).exists
  refine ⟨(M₀ : ℝ) + 1, by positivity, Filter.Eventually.of_forall fun n => ?_⟩
  calc P {ω | (M₀ : ℝ) + 1 ≤ ‖W (fun l => X ((n : ℤ) + l) ω)‖}
      = P {ω | (M₀ : ℝ) + 1 ≤ ‖Wproc 0 ω‖} := huniform _ (n : ℤ)
    _ ≤ P {ω | (M₀ : ℝ) ≤ ‖Wproc 0 ω‖} := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        linarith
    _ ≤ δ := le_of_lt hM₀

/-- **Boundary-correction engine (shared).** Given the shifted-partial-sum limit
`(√n)⁻¹ ∑_{t<n} u₍ₜ₊₁₎ ⇒ L` and score tightness `Oₚ(1)`, the un-shifted partial sum
`(√n)⁻¹ ∑_{t<n} uₜ` has the same limit. The two differ by the boundary term `(√n)⁻¹(u₀ − uₙ)`, which
vanishes in probability. This is the generic core of `sampleScore_tendstoInDistribution`, agnostic
to whether the shifted CLT is supplied by the MDS bundle (Theorem 14.30) or the mixing bundle
(Theorems 14.32/14.35(c)). -/
private theorem sampleSum_unshift_tendstoInDistribution
    {ι : Type*} [Fintype ι] {u : ℤ → Ω → (ι → ℝ)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {L : Ω' → (ι → ℝ)}
    (humeas : ∀ t : ℤ, AEMeasurable (u t) P)
    (hbdd : BoundedInProbabilityNorm P (fun n ω => u (n : ℤ) ω))
    (hshift : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)
      atTop L (fun _ => P) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, u (t : ℤ) ω)
      atTop L (fun _ => P) P' := by
  classical
  have hc0 : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hTmeas : ∀ n : ℕ,
      AEMeasurable (fun ω => (Real.sqrt (n : ℝ))⁻¹ •
        ∑ t ∈ Finset.range n, u (t : ℤ) ω) P := fun n =>
    (Finset.aemeasurable_fun_sum (Finset.range n) fun (t : ℕ) _ =>
      humeas (t : ℤ)).const_smul ((Real.sqrt (n : ℝ))⁻¹)
  have hrem_u0 : TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) => (Real.sqrt (n : ℝ))⁻¹ • u 0 ω) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae
      (fun n => ((humeas 0).const_smul ((Real.sqrt (n : ℝ))⁻¹)).aestronglyMeasurable)
      (ae_of_all _ fun ω => by simpa using hc0.smul_const (u 0 ω))
  have hrem_un : TendstoInMeasure P
      (fun (n : ℕ) ω => (-(Real.sqrt (n : ℝ))⁻¹) • u (n : ℤ) ω) atTop (fun _ => 0) :=
    hbdd.tendstoInMeasure_const_smul_zero (by simpa using hc0.neg)
  have hA : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω
        + (Real.sqrt (n : ℝ))⁻¹ • u 0 ω)
      atTop L (fun _ => P) P' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hshift ?_ ?_
    · refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hrem_u0
      exact ae_of_all _ fun ω => by simp [Pi.sub_apply]
    · exact fun n =>
        ((Finset.aemeasurable_fun_sum (Finset.range n)
          fun (t : ℕ) _ => humeas ((t : ℤ) + 1)).const_smul ((Real.sqrt (n : ℝ))⁻¹)).add
          ((humeas 0).const_smul ((Real.sqrt (n : ℝ))⁻¹))
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hA ?_ hTmeas
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hrem_un
  refine ae_of_all _ fun ω => ?_
  have key : (∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω) + u 0 ω
      = (∑ t ∈ Finset.range n, u (t : ℤ) ω) + u (n : ℤ) ω := by
    have h0 : u 0 ω = (fun j : ℕ => u (j : ℤ) ω) 0 := by norm_num
    have hs : (∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)
        = ∑ t ∈ Finset.range n, (fun j : ℕ => u (j : ℤ) ω) (t + 1) :=
      Finset.sum_congr rfl fun t _ => by norm_cast
    rw [h0, hs, ← Finset.sum_range_succ' (fun j : ℕ => u (j : ℤ) ω) n,
      Finset.sum_range_succ (fun j : ℕ => u (j : ℤ) ω) n]
  have hB : (∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)
      = (∑ t ∈ Finset.range n, u (t : ℤ) ω) + u (n : ℤ) ω - u 0 ω :=
    eq_sub_of_add_eq key
  simp only [Pi.sub_apply, hB]
  module

/-- **Least-squares Slutsky assembly (shared engine).** Over an abstract sample Gram `Ĝₙ`,
cross-moment `ĉₙ`, population Gram `Q` (nonsingular), coefficient `β`, and score summand, given
`Q̂ₙ →ₚ Q` (`hĜtend`), the a.e. score-average bridge `ĉₙ = Q̂ₙ β + n⁻¹ ∑ score` (`hbridge`), and the
normalized score central limit theorem `(√n)⁻¹ ∑ score ⇒ Z` (`hscoreCLT`), the least-squares
estimator `β̂ₙ = Q̂ₙ⁻¹ ĉₙ` is asymptotically normal: `√n(β̂ₙ − β) ⇒ Q⁻¹ Z`. The proof is the
random-inverse composition `matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix` (giving
`Q̂ₙ⁻¹·(√n · score-avg) ⇒ Q⁻¹ Z`) together with the singular-event residual: on `{det Q̂ₙ ≠ 0}` the
bridge and `Q̂ₙ⁻¹ Q̂ₙ = 1` make `√n(β̂ₙ − β)` coincide with `Q̂ₙ⁻¹·(√n · score-avg)`, and the gap is
supported on `{det Q̂ₙ = 0}`, whose probability tends to `0`. This is the generic form of Theorem
14.30's assembly (`arLS_residual_tendstoInMeasure_zero` + the final Slutsky step), consumed by
Theorems 14.32 and 14.35(b)(c). -/
private theorem leastSquares_asymptoticNormal_of_scoreCLT
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ĝ : ℕ → Ω → Matrix ι ι ℝ} {ĉ : ℕ → Ω → (ι → ℝ)} {Q : Matrix ι ι ℝ} {β : ι → ℝ}
    {score : ℕ → Ω → (ι → ℝ)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → (ι → ℝ)}
    (hQ : IsUnit Q.det)
    (hĜmeas : ∀ n, AEStronglyMeasurable (fun ω => Ĝ n ω) P)
    (hĉmeas : ∀ n, AEStronglyMeasurable (fun ω => ĉ n ω) P)
    (hĜtend : TendstoInMeasure P (fun n ω => Ĝ n ω) atTop (fun _ => Q))
    (hbridge : ∀ n, (fun ω => ĉ n ω) =ᵐ[P]
      fun ω => Ĝ n ω *ᵥ β + (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, score t ω)
    (hscoreCLT : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, score t ω)
      atTop Z (fun _ => P) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • ((Ĝ n ω)⁻¹ *ᵥ ĉ n ω - β))
      atTop (fun ω' => Q⁻¹ *ᵥ Z ω') (fun _ => P) P' := by
  classical
  have hne : Q.det ≠ 0 := isUnit_iff_ne_zero.mp hQ
  have hβStarmeas : ∀ n, AEStronglyMeasurable (fun ω => (Ĝ n ω)⁻¹ *ᵥ ĉ n ω) P := fun n =>
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((aestronglyMeasurable_matrix_inv (hĜmeas n)).prodMk (hĉmeas n))
  -- Singular-event residual.
  have hsc : ∀ n : ℕ, Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
    intro n
    rcases eq_or_ne (n : ℝ) 0 with hn | hn
    · simp [hn]
    · have hpos : (0 : ℝ) < n := lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)
      have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
      field_simp
      exact Real.sq_sqrt hpos.le
  have hresid : TendstoInMeasure P
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • ((Ĝ n ω)⁻¹ *ᵥ ĉ n ω - β)
        - (Ĝ n ω)⁻¹ *ᵥ ((Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, score t ω))
      atTop (fun _ => 0) := by
    have hdet_tend : TendstoInMeasure P (fun n ω => (Ĝ n ω).det) atTop (fun _ => Q.det) :=
      tendstoInMeasure_continuous_comp hĜmeas hĜtend (Continuous.matrix_det continuous_id)
    have hdet0 : Tendsto (fun n => P {ω | (Ĝ n ω).det = 0}) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hdet_tend (ENNReal.ofReal |Q.det|) (ENNReal.ofReal_pos.mpr (abs_pos.mpr hne)))
        (fun _ => zero_le _) (fun n => ?_)
      refine measure_mono (fun ω hω => ?_)
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdet0
      (fun _ => zero_le _) (fun n => ?_)
    refine measure_mono_ae ?_
    filter_upwards [hbridge n] with ω hbridgeω hle
    by_contra hdetω
    have hUn : IsUnit (Ĝ n ω).det := isUnit_iff_ne_zero.mpr hdetω
    have hR : Real.sqrt (n : ℝ) • ((Ĝ n ω)⁻¹ *ᵥ ĉ n ω - β)
        - (Ĝ n ω)⁻¹ *ᵥ ((Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, score t ω) = 0 := by
      rw [hbridgeω, Matrix.mulVec_add, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hUn, Matrix.one_mulVec, add_sub_cancel_left,
        Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, hsc n, sub_self]
    have hle2 : ε ≤ edist (Real.sqrt (n : ℝ) • ((Ĝ n ω)⁻¹ *ᵥ ĉ n ω - β)
        - (Ĝ n ω)⁻¹ *ᵥ ((Real.sqrt (n : ℝ))⁻¹ •
            ∑ t ∈ Finset.range n, score t ω)) 0 := hle
    rw [hR, edist_self] at hle2
    exact absurd hle2 (not_le.mpr hε)
  have hcomp := matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix
    hscoreCLT hĜmeas hĜtend hQ
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hcomp hresid (fun n => ?_)
  exact (((hβStarmeas n).sub aestronglyMeasurable_const).const_smul
    (Real.sqrt (n : ℝ))).aemeasurable

omit [IsProbabilityMeasure P] in
/-- **Score-average bridge for the projection fit (Hansen §14.32).** With the AR(p) fit taken to be
the best linear predictor `α`, the projection error `eₜ = Yₜ − xₜ ⬝ α` makes the recursion
`Yₜ = xₜ ⬝ α + eₜ` an identity, so the sample cross-moment splits as `ĉₙ = Q̂ₙ α + n⁻¹ ∑ eₜ xₜ`
without any distributional assumption on `e`. This is `arCrossHat_ae_eq` specialized to a
definitional recursion (no `ARModelConditions` needed), feeding the shared Slutsky engine. -/
private theorem arCrossHat_ae_eq_proj (α : Fin (p + 1) → ℝ) (n : ℕ) :
    (fun ω => arCrossHat Y p n ω) =ᵐ[P] fun ω => arGramHat Y p n ω *ᵥ α
      + (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n,
          (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ α) • arDesign Y p (t : ℤ) ω := by
  refine ae_of_all _ fun ω => ?_
  simp only [arCrossHat, arGramHat, smul_mulVec, sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  rw [← smul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun t ht => ?_)
  rw [← add_smul, show arDesign Y p (t : ℤ) ω ⬝ᵥ α + (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ α)
      = Y (t : ℤ) ω from by ring]

/-- **Hansen Theorem 14.32 (asymptotic normality of the AR(p) least-squares estimator under general
dependence).** For a strictly stationary, ergodic, `Lʳ`-integrable (`r > 4`) α-mixing process `Y`
whose mixing coefficients satisfy `∑ α(ℓ)^{1−4/r} < ∞` (bundle `ARMixingConditions`), conditional on
the vector α-mixing central limit theorem for the score `wₜ = eₜ xₜ`
(`eₜ = Yₜ − xₜ ⬝ arProjCoeff Y P p` the projection error; bundle `MixingCLTConditionsVec`, Hansen
Theorem 14.15), the least-squares estimator is asymptotically normal:
`√n(α̂ₙ − α) ⇒ N(0, Q⁻¹ Ω Q⁻¹)`, where `Q = arGram Y P p` is the design second-moment matrix
(positive definite by Theorem 14.28), `Ω = hclt.covMat` is the score's long-run covariance matrix
(well defined by `summable_autocov_scoreProj_of_mixing`), and `α = arProjCoeff Y P p`. Unlike
Theorem 14.30 the innovation need not be a martingale difference sequence — the mixing CLT replaces
the martingale-difference CLT — so the sandwich is genuinely `Q⁻¹ Ω Q⁻¹` with `Ω` the long-run
(rather than one-step) score covariance.

The limit is phrased in the repository's reference-random-variable idiom, exactly as Theorem 14.30:
the image `ω' ↦ Q⁻¹ ·(Z ω')` of any reference variable `Z` with
`HasLaw Z (multivariateGaussian 0 Ω)`. The proof is the shared Slutsky assembly
`leastSquares_asymptoticNormal_of_scoreCLT`, fed by the mixing vector CLT
(`MixingCLTConditionsVec.central_limit`) through the boundary correction
`sampleSum_unshift_tendstoInDistribution` (with score tightness from
`boundedInProbabilityNorm_shiftEquivariant`) and the projection-fit bridge `arCrossHat_ae_eq_proj`.
-/
theorem arLS_asymptoticNormal_mixing {r : ℝ} (h : ARMixingConditions Y P p r)
    (hclt : MixingCLTConditionsVec
      (fun t ω => (Y t ω - arDesign Y p t ω ⬝ᵥ arProjCoeff Y P p) • arDesign Y p t ω) P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → EuclideanSpace ℝ (Fin (p + 1))}
    (hZ : HasLaw Z (multivariateGaussian 0 hclt.covMat) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (arLSStar Y p n ω - arProjCoeff Y P p))
      atTop (fun ω' => (arGram Y P p)⁻¹ *ᵥ (Z ω').ofLp) (fun _ => P) P' := by
  classical
  have hmeasAE : ∀ t, AEMeasurable (Y t) P := fun t => (h.meas t).aemeasurable
  have hdetU : IsUnit (arGram Y P p).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h.gram_posDef.isUnit
  have hCLT := hclt.central_limit hZ
  set α := arProjCoeff Y P p with hα
  set w : ℤ → Ω → (Fin (p + 1) → ℝ) :=
    fun t ω => (Y t ω - arDesign Y p t ω ⬝ᵥ α) • arDesign Y p t ω with hw
  have hle2 : (2 : ENNReal) ≤ ENNReal.ofReal r := by
    have hh := ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ r by linarith [h.hr]); simpa using hh
  have hL2 : ∀ s, MemLp (Y s) 2 P := fun s =>
    (identDistrib_arCoord h.stationary s).memLp_iff.mpr (h.memLp.mono_exponent hle2)
  -- score measurability
  have hwmeas : ∀ t : ℤ, AEMeasurable (w t) P := fun t =>
    (((h.meas t).sub (measurable_arDesign_dotProduct h.meas t α)).aemeasurable).smul
      (aestronglyMeasurable_arDesign hmeasAE p t).aemeasurable
  -- shifted-sum CLT in plain-vector coordinates
  have hS : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, w ((t : ℤ) + 1) ω)
      atTop (fun z => (Z z).ofLp) (fun _ => P) P' := by
    have hMap := TendstoInDistribution.continuous_comp
      (g := (WithLp.ofLp : EuclideanSpace ℝ (Fin (p + 1)) → (Fin (p + 1) → ℝ)))
      (PiLp.continuous_ofLp 2 (fun _ => ℝ)) hCLT
    simpa [Function.comp_def] using hMap
  -- score tightness via the shift-equivariant functional
  have hbdd : BoundedInProbabilityNorm P (fun n ω => w (n : ℤ) ω) := by
    set W : (ℤ → ℝ) → (Fin (p + 1) → ℝ) :=
      fun y => (y 0 - arDesignPath p y ⬝ᵥ α) • arDesignPath p y with hW
    have hWmeas : Measurable W := by
      rw [hW]
      refine measurable_pi_iff.mpr fun i => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      refine Measurable.mul ((measurable_pi_apply 0).sub ?_) (measurable_arDesignPath_apply p i)
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun k _ =>
        (measurable_arDesignPath_apply p k).mul_const (α k)
    have heq : (fun (n : ℕ) ω => w (n : ℤ) ω)
        = fun (n : ℕ) ω => W (fun l => Y ((n : ℤ) + l) ω) := by
      funext n ω
      simp only [hw, hW, ← arDesign_eq_path Y p (n : ℤ) ω, add_zero]
    rw [heq]
    exact boundedInProbabilityNorm_shiftEquivariant h.stationary hmeasAE hWmeas
  -- boundary correction, then the shared Slutsky assembly
  have hscoreCLT := sampleSum_unshift_tendstoInDistribution hwmeas hbdd hS
  exact leastSquares_asymptoticNormal_of_scoreCLT hdetU
    (fun n => aestronglyMeasurable_arGramHat hmeasAE p n)
    (fun n => aestronglyMeasurable_arCrossHat hmeasAE p n)
    (arGramHat_tendsto h.ergodic hmeasAE hL2 p)
    (fun n => arCrossHat_ae_eq_proj α n) hscoreCLT

/-! ### Theorem 14.35(b)(c): asymptotic normality of a time-series regression

Both normality parts of Hansen Theorem 14.35 share the consistency skeleton with a generic design.
The score is the regression moment `Xₜ eₜ = Xₜ (Yₜ − Xₜ ⬝ β)` with `β = tsBeta Z P` the projection
coefficient (`tsScore`); part (b) supplies its CLT via the martingale-difference bundle
`MDSCLTConditionsVec` (the innovation is an MDS), part (c) via the α-mixing bundle
`MixingCLTConditionsVec`. The two endpoints share a single private core
`tsRegression_normal_of_shift`, which runs the boundary correction and the Slutsky assembly, so the
Slutsky chain is written once. -/

/-- **The time-series regression score** `Xₜ eₜ = Xₜ (Yₜ − Xₜ ⬝ β)` (outcome `Yₜ = Zₜ 0`, regressors
`Xₜ = (Zₜ 1, …, Zₜ k)`, `β = tsBeta Z P`), the `Fin k → ℝ`-valued moment process whose central limit
theorem drives the asymptotic normality of `β̂ₙ` (Hansen 14.35(b)(c)). -/
noncomputable def tsScore (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (P : Measure Ω) (t : ℤ) (ω : Ω) :
    Fin k → ℝ :=
  (Z t ω 0 - (fun i => Z t ω i.succ) ⬝ᵥ tsBeta Z P) • (fun i => Z t ω i.succ)

omit [IsProbabilityMeasure P] in
/-- **Score-average bridge for the time-series regression (Hansen §14.35).** The projection error
`eₜ = Yₜ − Xₜ ⬝ β` makes `Yₜ = Xₜ ⬝ β + eₜ` an identity, so `ĉₙ = Q̂ₙ β + n⁻¹ ∑ Xₜ eₜ`. This is the
generic-design analogue of `arCrossHat_ae_eq_proj`, feeding the shared Slutsky engine. -/
private theorem tsCrossHat_ae_eq_proj (Z : ℤ → Ω → (Fin (k + 1) → ℝ)) (n : ℕ) :
    (fun ω => tsCrossHat Z n ω) =ᵐ[P] fun ω => tsGramHat Z n ω *ᵥ tsBeta Z P
      + (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n, tsScore Z P (t : ℤ) ω := by
  refine ae_of_all _ fun ω => ?_
  simp only [tsCrossHat, tsGramHat, tsScore, smul_mulVec, sum_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul]
  rw [← smul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun t ht => ?_)
  rw [← add_smul, show (fun i => Z (t : ℤ) ω i.succ) ⬝ᵥ tsBeta Z P
      + (Z (t : ℤ) ω 0 - (fun i => Z (t : ℤ) ω i.succ) ⬝ᵥ tsBeta Z P) = Z (t : ℤ) ω 0 from by ring]

omit [IsProbabilityMeasure P] in
/-- Coordinate measurability of the time-series score. -/
private theorem aemeasurable_tsScore {Z : ℤ → Ω → (Fin (k + 1) → ℝ)}
    (h : TSRegressionConditions Z P) (t : ℤ) : AEMeasurable (tsScore Z P t) P := by
  have hscalar : AEMeasurable
      (fun ω => Z t ω 0 - (fun i => Z t ω i.succ) ⬝ᵥ tsBeta Z P) P := by
    refine ((measurable_pi_apply 0).comp_aemeasurable (h.meas t)).sub ?_
    simp only [dotProduct]
    exact Finset.aemeasurable_fun_sum _ fun i _ =>
      (((measurable_pi_apply i.succ).comp_aemeasurable (h.meas t)).mul_const (tsBeta Z P i))
  exact hscalar.smul (aestronglyMeasurable_tsRegressors h t).aemeasurable

/-- **Shared time-series normality core (Hansen §14.35).** Given the shifted-partial-sum limit
`(√n)⁻¹ ∑ Xₜ₊₁ eₜ₊₁ ⇒ L` of the regression score, the least-squares estimator is asymptotically
normal: `√n(β̂ₙ − β) ⇒ Q⁻¹ L`. The proof supplies the score tightness
(`boundedInProbabilityNorm_shiftEquivariant`), applies the boundary correction
(`sampleSum_unshift_tendstoInDistribution`) and the Slutsky assembly
(`leastSquares_asymptoticNormal_of_scoreCLT`) through the regression bridge
(`tsCrossHat_ae_eq_proj`). Both 14.35(b) and 14.35(c) instantiate it with their respective
shifted-sum CLTs, so the Slutsky chain is written once. -/
private theorem tsRegression_normal_of_shift {Z : ℤ → Ω → (Fin (k + 1) → ℝ)}
    (h : TSRegressionConditions Z P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Zref : Ω' → EuclideanSpace ℝ (Fin k)}
    (hS : TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ • ∑ t ∈ Finset.range n, tsScore Z P ((t : ℤ) + 1) ω)
      atTop (fun z => (Zref z).ofLp) (fun _ => P) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (tsBetaStar Z n ω - tsBeta Z P))
      atTop (fun ω' => (tsGram Z P)⁻¹ *ᵥ (Zref ω').ofLp) (fun _ => P) P' := by
  classical
  have hdetU : IsUnit (tsGram Z P).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h.posDef.isUnit
  have hscoremeas : ∀ t : ℤ, AEMeasurable (tsScore Z P t) P := fun t => aemeasurable_tsScore h t
  -- score tightness via the shift-equivariant functional of the joint process
  have hbdd : BoundedInProbabilityNorm P (fun n ω => tsScore Z P (n : ℤ) ω) := by
    set W : (ℤ → (Fin (k + 1) → ℝ)) → (Fin k → ℝ) :=
      fun y => (y 0 0 - (fun i => y 0 i.succ) ⬝ᵥ tsBeta Z P) • (fun i => y 0 i.succ) with hW
    have hy0 : Measurable (fun y : ℤ → (Fin (k + 1) → ℝ) => y 0) := measurable_pi_apply 0
    have hWmeas : Measurable W := by
      rw [hW]
      refine measurable_pi_iff.mpr fun i => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      refine Measurable.mul (((measurable_pi_apply 0).comp hy0).sub ?_)
        ((measurable_pi_apply i.succ).comp hy0)
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (((measurable_pi_apply j.succ).comp hy0).mul_const (tsBeta Z P j))
    have heq : (fun (n : ℕ) ω => tsScore Z P (n : ℤ) ω)
        = fun (n : ℕ) ω => W (fun l => Z ((n : ℤ) + l) ω) := by
      funext n ω; simp only [tsScore, hW, add_zero]
    rw [heq]
    exact boundedInProbabilityNorm_shiftEquivariant h.stationary h.meas hWmeas
  have hscoreCLT := sampleSum_unshift_tendstoInDistribution hscoremeas hbdd hS
  exact leastSquares_asymptoticNormal_of_scoreCLT hdetU
    (fun n => aestronglyMeasurable_tsGramHat h n) (fun n => aestronglyMeasurable_tsCrossHat h n)
    (tsGramHat_tendsto h) (fun n => tsCrossHat_ae_eq_proj Z n) hscoreCLT

/-- **Hansen Theorem 14.35(b) (time-series regression normality, martingale-difference case).**
Under the standing `TSRegressionConditions`, conditional on the vector martingale-difference central
limit theorem for the regression score `Xₜ eₜ` (bundle `MDSCLTConditionsVec`, i.e. the innovation is
a martingale difference sequence), the least-squares estimator is asymptotically normal:
`√n(β̂ₙ − β) ⇒ N(0, Q⁻¹ Σ Q⁻¹)`, with `Q = tsGram Z P`, `Σ = hclt.covMat`, and `β = tsBeta Z P`. It
is the direct time-series-regression analogue of Theorem 14.30, assembled through the shared core
`tsRegression_normal_of_shift`. -/
theorem tsRegression_asymptoticNormal {Z : ℤ → Ω → (Fin (k + 1) → ℝ)}
    (h : TSRegressionConditions Z P) {ℱ : Filtration ℤ ‹MeasurableSpace Ω›}
    (hclt : MDSCLTConditionsVec ℱ (tsScore Z P) P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Zref : Ω' → EuclideanSpace ℝ (Fin k)}
    (hZref : HasLaw Zref (multivariateGaussian 0 hclt.covMat) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (tsBetaStar Z n ω - tsBeta Z P))
      atTop (fun ω' => (tsGram Z P)⁻¹ *ᵥ (Zref ω').ofLp) (fun _ => P) P' := by
  refine tsRegression_normal_of_shift h ?_
  have hMap := TendstoInDistribution.continuous_comp
    (g := (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → (Fin k → ℝ)))
    (PiLp.continuous_ofLp 2 (fun _ => ℝ)) (hclt.central_limit hZref)
  simpa [Function.comp_def] using hMap

/-- **Hansen Theorem 14.35(c) (time-series regression normality, α-mixing case).** Under the
standing `TSRegressionConditions`, conditional on the vector α-mixing central limit theorem for the
regression score `Xₜ eₜ` (bundle `MixingCLTConditionsVec`), the least-squares estimator is
asymptotically normal: `√n(β̂ₙ − β) ⇒ N(0, Q⁻¹ Ω Q⁻¹)`, with `Q = tsGram Z P`, `Ω = hclt.covMat` the
score's long-run covariance matrix, and `β = tsBeta Z P`. The mixing analogue of part (b): the
innovation need not be a martingale difference sequence, and the long-run (rather than one-step)
score covariance appears. It is assembled through the same shared core
`tsRegression_normal_of_shift`. -/
theorem tsRegression_asymptoticNormal_mixing {Z : ℤ → Ω → (Fin (k + 1) → ℝ)}
    (h : TSRegressionConditions Z P)
    (hclt : MixingCLTConditionsVec (tsScore Z P) P)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Zref : Ω' → EuclideanSpace ℝ (Fin k)}
    (hZref : HasLaw Zref (multivariateGaussian 0 hclt.covMat) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) • (tsBetaStar Z n ω - tsBeta Z P))
      atTop (fun ω' => (tsGram Z P)⁻¹ *ᵥ (Zref ω').ofLp) (fun _ => P) P' := by
  refine tsRegression_normal_of_shift h ?_
  have hMap := TendstoInDistribution.continuous_comp
    (g := (WithLp.ofLp : EuclideanSpace ℝ (Fin k) → (Fin k → ℝ)))
    (PiLp.continuous_ofLp 2 (fun _ => ℝ)) (hclt.central_limit hZref)
  simpa [Function.comp_def] using hMap

end MixingNormality

/-! ### Theorems 14.33 and 14.34: covariance-matrix estimation for the AR(p) least-squares estimator

Hansen **Theorem 14.33** estimates the asymptotic covariance matrix of the AR(p) least-squares
estimator. The estimator-consistency core is landed in full; the studentized t-ratio (14.33(b)) and
the Newey–West/HAC estimator (Theorem 14.34) are documented deferrals.

**Textual-slip flag (campaign-mandated).** Hansen's text states Theorem 14.33 "under the assumptions
of Theorem 14.32", but the estimator constructed there is the correctly-specified,
martingale-difference one — the homoskedastic sandwich `σ̂² Q̂⁻¹`, whose limit is `σ² Q⁻¹` from
Theorem 14.31 — not the long-run-variance sandwich `Q⁻¹ Ω Q⁻¹` of the α-mixing case (Theorem 14.32).
We therefore formalize Theorem 14.33 against **Theorem 14.30's** hypotheses (`ARModelConditions`),
and each declaration below carries this note.

**Part (a) — estimator consistency (fully proved).** `ProbabilityTheory.arSigmaSqHat_consistent`
shows the residual variance `σ̂²ₙ = (1/n) ∑_{t<n}(Yₜ − xₜ ⬝ α̂ₙ)²` converges in probability to the
innovation variance `𝔼[e₀²]`, and `ProbabilityTheory.arVHat_consistent` shows the homoskedastic
covariance-matrix estimator `V̂⁰ₙ = σ̂²ₙ Q̂ₙ⁻¹` converges to `𝔼[e₀²] · Q⁻¹` (the `σ² Q⁻¹` of Theorem
14.31). The residual-correction algebra is the *exact pointwise identity*
(`arSigmaSqHatStar_decomp`) `σ̂²ₙ = (1/n)∑ eₜ² − 2 (α̂ₙ − α) ⬝ ĝₙ + (α̂ₙ − α) ⬝ Q̂ₙ (α̂ₙ − α)` with
`eₜ = Yₜ − xₜ ⬝ α`: the leading term converges to `𝔼[e₀²]` by the ergodic LLN
(`arResidVar_tendsto`), and the two correction terms vanish because `α̂ₙ − α →ₚ 0`
(`arLSStar_tendsto_coeff`, the Theorem 14.29 consistency engine) multiplies `Oₚ(1)` sample moments
(`TendstoInMeasure.mul_boundedInProbability`).

**Part (b) — studentized t-ratio (deferred, documented).** With part (a)'s `V̂⁰ₙ →ₚ σ² Q⁻¹` and
Theorem 14.31's `√n(α̂ₙ − α) ⇒ N(0, σ² Q⁻¹)`, the studentized coordinate `(α̂ₙ,ᵢ − αᵢ)/se_i`
(`se_i` from `V̂⁰ₙ / n`) is asymptotically standard normal by Slutsky. This is not formalized here:
Chapter 7's t-ratio idiom (`symmetricCI_coverage_of_abs_tstat` in `Chapter7Asymptotics.Inference`)
*consumes* a studentized `→d |N(0,1)|` hypothesis rather than producing one, and manufacturing it
(coordinate extraction from the vector limit plus a scalar `→d`/`→ₚ` ratio combinator, absent from
`AsymptoticUtils.DeltaMethod`) is a self-contained block the campaign classifies as conditional. It
follows morally from `arVHat_consistent` and `arLS_asymptoticNormal_homoskedastic` (14.31) jointly.

**Theorem 14.34 — Newey–West/HAC consistency (documented deferral).** Hansen gives no proof, citing
B. E. Hansen (1992); a Newey–West heteroskedasticity-and-autocorrelation-consistent
long-run-variance estimator requires kernel-HAC variance bounds under `∑ α(ℓ)^{1/2 − 4/r} < ∞` and
bandwidth asymptotics `M³/n = O(1)` — a research-paper-length argument with no Mathlib support (even
deterministic Bartlett-weight positive semidefiniteness is a Fejér-kernel argument). It is omitted.
-/

section CovarianceEstimation

/-- **The AR(p) residual-variance estimator** (Star convention): the mean squared least-squares
residual `σ̂²ₙ = (1/n) ∑_{t<n} (Yₜ − xₜ ⬝ α̂ₙ)²`, with `α̂ₙ = arLSStar Y p n` and
`xₜ = arDesign Y p t`. Its probability limit under `ARModelConditions` (Theorem 14.30's hypotheses;
see the textual-slip flag above) is the innovation variance `𝔼[e₀²]` (`arSigmaSqHat_consistent`). -/
noncomputable def arSigmaSqHatStar (Y : ℤ → Ω → ℝ) (p n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
    (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ arLSStar Y p n ω) ^ 2

/-- **The homoskedastic covariance-matrix estimator** `V̂⁰ₙ = σ̂²ₙ • Q̂ₙ⁻¹` (Star convention), the
sample analogue of Theorem 14.31's limiting sandwich `σ² Q⁻¹`. Under `ARModelConditions` it is
consistent for `𝔼[e₀²] • Q⁻¹` (`arVHat_consistent`). See the textual-slip flag above: this is the
correctly-specified (14.30/14.31) estimator, not the α-mixing (14.32) one. -/
noncomputable def arVHatStar (Y : ℤ → Ω → ℝ) (p n : ℕ) (ω : Ω) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ :=
  arSigmaSqHatStar Y p n ω • (arGramHat Y p n ω)⁻¹

/-- Sample cross-moment of the population-coefficient residual `Yₜ − xₜ ⬝ c` against the design,
`(1/n) ∑_{t<n} (Yₜ − xₜ ⬝ c) • xₜ`. Private scaffolding for the residual-variance decomposition. -/
private noncomputable def arResidCrossHat (Y : ℤ → Ω → ℝ) (p n : ℕ) (c : Fin (p + 1) → ℝ) (ω : Ω) :
    Fin (p + 1) → ℝ :=
  (n : ℝ)⁻¹ • ∑ t ∈ Finset.range n,
    (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ c) • arDesign Y p (t : ℤ) ω

omit [MeasurableSpace Ω] [IsFiniteMeasure P] in
/-- Entrywise value of the residual cross-moment. -/
private theorem arResidCrossHat_apply (Y : ℤ → Ω → ℝ) (p n : ℕ) (c : Fin (p + 1) → ℝ) (ω : Ω)
    (i : Fin (p + 1)) :
    arResidCrossHat Y p n c ω i
      = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
          (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ c) * arDesign Y p (t : ℤ) ω i := by
  simp only [arResidCrossHat, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

omit [MeasurableSpace Ω] [IsFiniteMeasure P] in
/-- **The residual-variance decomposition (Hansen §14.33(a), the residual-correction algebra).** The
exact pointwise identity behind `σ̂²`-consistency. Writing `ê_t = Y_t − x_t ⬝ α̂ₙ = e_t − x_t ⬝ δ`
with `δ = α̂ₙ − coeff` and `e_t = Y_t − x_t ⬝ coeff`, expanding the square splits `σ̂²ₙ` into the
mean squared population residual, a cross term `δ ⬝ (residual cross-moment)`, and a quadratic form
`δ ⬝ (Q̂ₙ δ)`. Holds for every `Y`, `p`, `n`, `coeff` — no distributional hypothesis. -/
private theorem arSigmaSqHatStar_decomp (Y : ℤ → Ω → ℝ) (p n : ℕ) (coeff : Fin (p + 1) → ℝ)
    (ω : Ω) :
    arSigmaSqHatStar Y p n ω
      = ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ coeff) ^ 2)
        - 2 * ∑ i, (arLSStar Y p n ω i - coeff i) * arResidCrossHat Y p n coeff ω i
        + ∑ i, ∑ j, (arLSStar Y p n ω i - coeff i) * arGramHat Y p n ω i j
            * (arLSStar Y p n ω j - coeff j) := by
  classical
  have hlin : ∀ t : ℕ, arDesign Y p (t : ℤ) ω ⬝ᵥ arLSStar Y p n ω
      = arDesign Y p (t : ℤ) ω ⬝ᵥ coeff
        + arDesign Y p (t : ℤ) ω ⬝ᵥ (arLSStar Y p n ω - coeff) := by
    intro t
    rw [← dotProduct_add]
    congr 1
    funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  have hsummand : ∀ t ∈ Finset.range n,
      (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ arLSStar Y p n ω) ^ 2
        = (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ coeff) ^ 2
          - 2 * ((Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ coeff)
              * (arDesign Y p (t : ℤ) ω ⬝ᵥ (arLSStar Y p n ω - coeff)))
          + (arDesign Y p (t : ℤ) ω ⬝ᵥ (arLSStar Y p n ω - coeff)) ^ 2 := by
    intro t _; rw [hlin t]; ring
  have hmid_vec : (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ coeff)
          * (arDesign Y p (t : ℤ) ω ⬝ᵥ (arLSStar Y p n ω - coeff))
      = ∑ i, (arLSStar Y p n ω i - coeff i) * arResidCrossHat Y p n coeff ω i := by
    have hvec : (arLSStar Y p n ω - coeff) ⬝ᵥ arResidCrossHat Y p n coeff ω
        = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
            (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ coeff)
              * (arDesign Y p (t : ℤ) ω ⬝ᵥ (arLSStar Y p n ω - coeff)) := by
      simp only [arResidCrossHat, dotProduct_smul, smul_eq_mul, dotProduct_sum]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [dotProduct_comm (arLSStar Y p n ω - coeff) (arDesign Y p (t : ℤ) ω)]
    rw [← hvec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply]
  have hquad_vec : (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        (arDesign Y p (t : ℤ) ω ⬝ᵥ (arLSStar Y p n ω - coeff)) ^ 2
      = ∑ i, ∑ j, (arLSStar Y p n ω i - coeff i) * arGramHat Y p n ω i j
          * (arLSStar Y p n ω j - coeff j) := by
    have hvec : (arLSStar Y p n ω - coeff) ⬝ᵥ (arGramHat Y p n ω *ᵥ (arLSStar Y p n ω - coeff))
        = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
            (arDesign Y p (t : ℤ) ω ⬝ᵥ (arLSStar Y p n ω - coeff)) ^ 2 := by
      simp only [arGramHat, smul_mulVec, sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
        dotProduct_smul, smul_eq_mul, dotProduct_sum]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [dotProduct_comm (arLSStar Y p n ω - coeff) (arDesign Y p (t : ℤ) ω), ← pow_two]
    rw [← hvec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [arSigmaSqHatStar]
  rw [Finset.sum_congr rfl hsummand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← hmid_vec, ← hquad_vec]
  ring

variable {Y e : ℤ → Ω → ℝ} {ℱ : Filtration ℤ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {p : ℕ} {coeff : Fin (p + 1) → ℝ}

/-- **AR(p) least-squares consistency under `ARModelConditions` (Theorem 14.30's hypotheses).** The
re-derivation of Theorem 14.29 that consumes the bundle's positive-definite design Gram
`h.gram_posDef` directly (rather than a positive prediction-error variance): `α̂ₙ →ₚ coeff`. This is
the `oₚ(1)`-factor supplier for the residual-variance correction terms in §14.33(a). -/
private theorem arLSStar_tendsto_coeff (h : ARModelConditions Y e ℱ P p coeff) :
    TendstoInMeasure P (fun n ω => arLSStar Y p n ω) atTop (fun _ => coeff) := by
  have hdet : IsUnit (arGram Y P p).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h.gram_posDef.isUnit
  have hInv := tendstoInMeasure_matrix_inv (fun n => aestronglyMeasurable_arGramHat h.meas p n)
    (arGramHat_tendsto h.ergodic h.meas h.memLp p) (fun _ => hdet)
  have hInv_meas : ∀ n, AEStronglyMeasurable (fun ω => (arGramHat Y p n ω)⁻¹) P :=
    fun n => aestronglyMeasurable_matrix_inv (aestronglyMeasurable_arGramHat h.meas p n)
  rw [← arProjCoeff_eq_coeff h]
  exact tendstoInMeasure_mulVec hInv_meas
    (fun n => aestronglyMeasurable_arCrossHat h.meas p n) hInv
    (arCrossHat_tendsto h.ergodic h.meas h.memLp p)

/-- **Residual-variance leading term (Hansen §14.33(a)).** The mean squared *population* residual
`(1/n) ∑_{t<n} (Yₜ − xₜ ⬝ coeff)²` converges in probability to the innovation variance `𝔼[e₀²]`. The
population residual `Y_t − x_t ⬝ coeff` is a shift-equivariant functional of `Y`, so the ergodic LLN
engine (`tendstoInMeasure_ergodicAverage_pathFunctional`) applies; the recursion identifies the
limit `∫(Y₀ − x₀⬝coeff)²` with `∫ e₀²`. -/
private theorem arResidVar_tendsto (h : ARModelConditions Y e ℱ P p coeff) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ coeff) ^ 2)
      atTop (fun _ => ∫ ω, (e 0 ω) ^ 2 ∂P) := by
  have hlinm : Measurable (fun y : ℤ → ℝ => y 0 - arDesignPath p y ⬝ᵥ coeff) := by
    refine (measurable_pi_apply 0).sub ?_
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ => (measurable_arDesignPath_apply p i).mul_const (coeff i)
  have hφ : Measurable (fun y : ℤ → ℝ => (y 0 - arDesignPath p y ⬝ᵥ coeff) ^ 2) := by
    simpa [pow_two] using hlinm.mul hlinm
  have hkey : ∀ (s : ℤ) (ω : Ω),
      (fun y : ℤ → ℝ => (y 0 - arDesignPath p y ⬝ᵥ coeff) ^ 2) (fun l => Y (s + l) ω)
        = (Y s ω - arDesign Y p s ω ⬝ᵥ coeff) ^ 2 := by
    intro s ω; simp only [← arDesign_eq_path Y p s ω, add_zero]
  have hint : Integrable (fun ω => (fun y : ℤ → ℝ => (y 0 - arDesignPath p y ⬝ᵥ coeff) ^ 2)
      (fun l => Y (0 + l) ω)) P := by
    have hL2r : MemLp (fun ω => Y 0 ω - arDesign Y p 0 ω ⬝ᵥ coeff) 2 P :=
      (h.memLp 0).sub (memLp_dotProduct_arDesign h.memLp p 0 coeff)
    have hprod : Integrable (fun ω => (Y 0 ω - arDesign Y p 0 ω ⬝ᵥ coeff) ^ 2) P := by
      refine (hL2r.integrable_mul hL2r).congr ?_
      filter_upwards with ω; rw [Pi.mul_apply]; ring
    refine hprod.congr ?_
    filter_upwards with ω; exact (hkey 0 ω).symm
  have hconv := tendstoInMeasure_ergodicAverage_pathFunctional h.ergodic h.meas hφ hint
  simp only [hkey] at hconv
  have hbridge : (∫ ω, (Y 0 ω - arDesign Y p 0 ω ⬝ᵥ coeff) ^ 2 ∂P) = ∫ ω, (e 0 ω) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [h.recursion 0] with ω hω; rw [hω]; ring
  refine hconv.congr' (Eventually.of_forall fun _ => EventuallyEq.rfl) ?_
  filter_upwards with ω; exact hbridge

/-- **Residual cross-moment convergence (Hansen §14.33(a)).** Each coordinate of the sample
cross-moment `(1/n) ∑_{t<n} (Yₜ − xₜ ⬝ coeff) xₜ,ᵢ` converges in probability to a finite constant
(`∫(Y₀ − x₀⬝coeff) x₀,ᵢ`), via the ergodic LLN engine on the `(p+1)`-lag functional. Only its
`Oₚ(1)` boundedness is used (against the `oₚ(1)` factor `α̂ₙ − coeff`). -/
private theorem arResidCross_entry_tendsto (h : ARModelConditions Y e ℱ P p coeff)
    (i : Fin (p + 1)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        (Y (t : ℤ) ω - arDesign Y p (t : ℤ) ω ⬝ᵥ coeff) * arDesign Y p (t : ℤ) ω i)
      atTop (fun _ => ∫ ω, (Y 0 ω - arDesign Y p 0 ω ⬝ᵥ coeff) * arDesign Y p 0 ω i ∂P) := by
  have hlinm : Measurable (fun y : ℤ → ℝ => y 0 - arDesignPath p y ⬝ᵥ coeff) := by
    refine (measurable_pi_apply 0).sub ?_
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun k _ => (measurable_arDesignPath_apply p k).mul_const (coeff k)
  have hφ : Measurable (fun y : ℤ → ℝ => (y 0 - arDesignPath p y ⬝ᵥ coeff) * arDesignPath p y i) :=
    hlinm.mul (measurable_arDesignPath_apply p i)
  have hkey : ∀ (s : ℤ) (ω : Ω),
      (fun y : ℤ → ℝ => (y 0 - arDesignPath p y ⬝ᵥ coeff) * arDesignPath p y i)
          (fun l => Y (s + l) ω)
        = (Y s ω - arDesign Y p s ω ⬝ᵥ coeff) * arDesign Y p s ω i := by
    intro s ω; simp only [← arDesign_eq_path Y p s ω, add_zero]
  have hint : Integrable (fun ω => (fun y : ℤ → ℝ => (y 0 - arDesignPath p y ⬝ᵥ coeff)
      * arDesignPath p y i) (fun l => Y (0 + l) ω)) P := by
    have hL2r : MemLp (fun ω => Y 0 ω - arDesign Y p 0 ω ⬝ᵥ coeff) 2 P :=
      (h.memLp 0).sub (memLp_dotProduct_arDesign h.memLp p 0 coeff)
    have hL2x : MemLp (fun ω => arDesign Y p 0 ω i) 2 P := memLp_arDesign_at h.memLp p 0 i
    have hprod : Integrable
        (fun ω => (Y 0 ω - arDesign Y p 0 ω ⬝ᵥ coeff) * arDesign Y p 0 ω i) P := by
      refine (hL2r.integrable_mul hL2x).congr ?_
      filter_upwards with ω; rw [Pi.mul_apply]
    refine hprod.congr ?_
    filter_upwards with ω; exact (hkey 0 ω).symm
  have hconv := tendstoInMeasure_ergodicAverage_pathFunctional h.ergodic h.meas hφ hint
  simp only [hkey] at hconv
  exact hconv

/-- **Hansen Theorem 14.33(a), residual-variance consistency.** Under `ARModelConditions` (Theorem
14.30's hypotheses — see the textual-slip flag: Hansen writes "14.32" but the estimator is the
correctly-specified/MDS one), the residual variance is consistent for the innovation variance:
`σ̂²ₙ →ₚ 𝔼[e₀²]`. The proof feeds the exact decomposition `arSigmaSqHatStar_decomp`: the leading
term converges by `arResidVar_tendsto`, and the cross and quadratic correction terms vanish because
`α̂ₙ − coeff →ₚ 0` (`arLSStar_tendsto_coeff`) multiplies `Oₚ(1)` sample moments
(`arResidCross_entry_tendsto`, `arGramHat_entry_tendsto`) through
`TendstoInMeasure.mul_boundedInProbability`. -/
theorem arSigmaSqHat_consistent (h : ARModelConditions Y e ℱ P p coeff) :
    TendstoInMeasure P (fun n ω => arSigmaSqHatStar Y p n ω) atTop
      (fun _ => ∫ ω, (e 0 ω) ^ 2 ∂P) := by
  classical
  have hδ : ∀ i, TendstoInMeasure P (fun n ω => arLSStar Y p n ω i - coeff i) atTop (fun _ => 0) :=
    fun i => TendstoInMeasure.sub_limit_zero_real
      (TendstoInMeasure.pi_apply (arLSStar_tendsto_coeff h) i)
  have hρbdd : ∀ i, BoundedInProbability P (fun n ω => arResidCrossHat Y p n coeff ω i) := fun i =>
    BoundedInProbability.of_tendstoInMeasure_const
      ((arResidCross_entry_tendsto h i).congr'
        (Eventually.of_forall fun n => ae_of_all P fun ω =>
          (arResidCrossHat_apply Y p n coeff ω i).symm) EventuallyEq.rfl)
  have hQbdd : ∀ i j, BoundedInProbability P (fun n ω => arGramHat Y p n ω i j) := fun i j =>
    BoundedInProbability.of_tendstoInMeasure_const
      ((arGramHat_entry_tendsto h.ergodic h.meas h.memLp p i j).congr'
        (Eventually.of_forall fun n => ae_of_all P fun ω => (arGramHat_apply Y p n ω i j).symm)
        EventuallyEq.rfl)
  have hmid0 : TendstoInMeasure P
      (fun n ω => ∑ i, (arLSStar Y p n ω i - coeff i) * arResidCrossHat Y p n coeff ω i)
      atTop (fun _ => 0) :=
    tendstoInMeasure_finset_sum_zero_real Finset.univ
      (fun i _ => TendstoInMeasure.mul_boundedInProbability (hδ i) (hρbdd i))
  have hquad0 : TendstoInMeasure P
      (fun n ω => ∑ i, ∑ j, (arLSStar Y p n ω i - coeff i) * arGramHat Y p n ω i j
        * (arLSStar Y p n ω j - coeff j)) atTop (fun _ => 0) := by
    refine tendstoInMeasure_finset_sum_zero_real Finset.univ fun i _ => ?_
    refine tendstoInMeasure_finset_sum_zero_real Finset.univ fun j _ => ?_
    refine (TendstoInMeasure.mul_boundedInProbability
      (TendstoInMeasure.mul_zero_real (hδ i) (hδ j)) (hQbdd i j)).congr'
        (Eventually.of_forall fun n => ae_of_all P fun ω => ?_) EventuallyEq.rfl
    ring
  have hcenter : TendstoInMeasure P
      (fun n ω => arSigmaSqHatStar Y p n ω - ∫ ω, (e 0 ω) ^ 2 ∂P) atTop (fun _ => 0) := by
    have hstep := TendstoInMeasure.add_zero_real
      (TendstoInMeasure.add_zero_real
        (TendstoInMeasure.sub_limit_zero_real (arResidVar_tendsto h))
        (TendstoInMeasure.neg_zero_real (TendstoInMeasure.const_mul_zero_real 2 hmid0)))
      hquad0
    refine hstep.congr' (Eventually.of_forall fun n => ae_of_all P fun ω => ?_) EventuallyEq.rfl
    simp only [arSigmaSqHatStar_decomp Y p n coeff]; ring
  exact TendstoInMeasure.of_sub_limit_zero_real hcenter

/-- **Hansen Theorem 14.33(a), covariance-matrix consistency.** Under `ARModelConditions` the
homoskedastic covariance-matrix estimator is consistent: `V̂⁰ₙ = σ̂²ₙ Q̂ₙ⁻¹ →ₚ 𝔼[e₀²] • Q⁻¹`
unconditionally; this limit is the correct asymptotic sandwich `σ² Q⁻¹` of Theorem 14.31 precisely
under conditional homoskedasticity `𝔼[eₜ² | ℱₜ₋₁] = σ²` (which this theorem does not assume — it is
the limit of the homoskedastic-*form* estimator regardless). Entrywise, `σ̂²ₙ →ₚ 𝔼[e₀²]`
(`arSigmaSqHat_consistent`) and `(Q̂ₙ⁻¹)ᵢⱼ →ₚ (Q⁻¹)ᵢⱼ` (the Theorem 14.29 inverse CMT,
`tendstoInMeasure_matrix_inv` with the positive-definite `Q`), so their product converges by
`TendstoInMeasure.mul_limits_real`; the joint matrix limit is reassembled by `tendstoInMeasure_pi`.
Textual-slip flag as in `arSigmaSqHat_consistent`. -/
theorem arVHat_consistent (h : ARModelConditions Y e ℱ P p coeff) :
    TendstoInMeasure P (fun n ω => arVHatStar Y p n ω) atTop
      (fun _ => (∫ ω, (e 0 ω) ^ 2 ∂P) • (arGram Y P p)⁻¹) := by
  have hdet : IsUnit (arGram Y P p).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h.gram_posDef.isUnit
  have hInv := tendstoInMeasure_matrix_inv (fun n => aestronglyMeasurable_arGramHat h.meas p n)
    (arGramHat_tendsto h.ergodic h.meas h.memLp p) (fun _ => hdet)
  have hσ := arSigmaSqHat_consistent h
  refine tendstoInMeasure_pi fun i => tendstoInMeasure_pi fun j => ?_
  have hInvij := TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hInv i) j
  refine (TendstoInMeasure.mul_limits_real hσ hInvij).congr'
    (Eventually.of_forall fun n => ae_of_all P fun ω => ?_) (ae_of_all P fun ω => ?_)
  · simp only [arVHatStar, Matrix.smul_apply, smul_eq_mul]
  · simp only [Matrix.smul_apply, smul_eq_mul]

end CovarianceEstimation

end LSAsymptotics

end ProbabilityTheory
