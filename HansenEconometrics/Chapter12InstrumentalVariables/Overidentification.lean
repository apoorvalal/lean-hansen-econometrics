import Mathlib.LinearAlgebra.Matrix.SchurComplement
import HansenEconometrics.ChiSquared
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.Chapter12InstrumentalVariables.Basic
import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics
import HansenEconometrics.Chapter9HypothesisTesting

/-!
# Chapter 12 — overidentification tests

This file contains the Sargan and subset-overidentification statistic surface
for Hansen Theorems 12.16 and 12.17.  The statistic definitions use the existing
Chapter 12 2SLS residuals and projection notation.  The observed-row
Assumption 12.2 endpoint with derived scalar variance positivity derives the
score, covariance, projection-rank, and variance-positivity inputs, fully
closing Theorem 12.16 under its displayed assumptions.

The canonical observed-row Theorem 12.17 endpoint derives the limiting row
rank and every finite-sample rank-failure probability from Assumption 12.2. It
proves `N = C*` on the nonsingular branch, shows equality failure has
probability tending to zero under totalization, and supplies both chi-square
limits, asymptotic equivalence, and calibrated test size through Chapter 9's
rejection bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Matrix MatrixOrder Matrix.Norms.Elementwise Topology
  MeasureTheory ProbabilityTheory

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

variable {n k l la lb : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype k] [DecidableEq k]
variable [Fintype l] [DecidableEq l]
variable [Fintype la] [DecidableEq la]
variable [Fintype lb] [DecidableEq lb]

section MatrixWoodburyHelpers

variable {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

private theorem nonsingInv_neg_of_invertible
    (A : Matrix p p ℝ) [Invertible A] :
    (-A)⁻¹ = -A⁻¹ := by
  letI : Invertible (-A) := invertibleNeg A
  rw [← invOf_eq_nonsing_inv (-A), invOf_neg, invOf_eq_nonsing_inv A]

private theorem woodbury_sub_nonsingInv
    (G : Matrix p p ℝ) (U : Matrix p q ℝ) (S A : Matrix q q ℝ) (V : Matrix q p ℝ)
    [Invertible G] [Invertible S] [Invertible A]
    [Invertible (G - U * S⁻¹ * V)]
    (hA : A = S - V * G⁻¹ * U) :
    (G - U * S⁻¹ * V)⁻¹ =
      G⁻¹ + G⁻¹ * U * A⁻¹ * V * G⁻¹ := by
  let C : Matrix q q ℝ := -S⁻¹
  letI : Invertible S⁻¹ := by infer_instance
  letI : Invertible C := by
    dsimp [C]
    exact invertibleNeg (S⁻¹)
  have hbridge : C⁻¹ + V * G⁻¹ * U = -A := by
    dsimp [C]
    rw [nonsingInv_neg_of_invertible (S⁻¹), Matrix.inv_inv_of_invertible]
    rw [hA]
    abel
  letI : Invertible (⅟C + V * ⅟G * U) := by
    have hbridge' : ⅟C + V * ⅟G * U = -A := by
      simpa [invOf_eq_nonsing_inv] using hbridge
    rw [hbridge']
    exact invertibleNeg A
  have hleft : G + U * C * V = G - U * S⁻¹ * V := by
    dsimp [C]
    rw [sub_eq_add_neg]
    congr 1
    rw [Matrix.mul_neg, Matrix.neg_mul]
  letI : Invertible (G + U * C * V) := by
    rw [hleft]
    infer_instance
  have hwb : ⅟(G + U * C * V) =
      ⅟G - ⅟G * U * ⅟(⅟C + V * ⅟G * U) * V * ⅟G :=
    Matrix.invOf_add_mul_mul (A := G) (U := U) (C := C) (V := V)
  have hwbN : (G + U * C * V)⁻¹ =
      G⁻¹ - G⁻¹ * U * (⅟(⅟C + V * ⅟G * U)) * V * G⁻¹ := by
    simpa [invOf_eq_nonsing_inv] using hwb
  calc
    (G - U * S⁻¹ * V)⁻¹ = (G + U * C * V)⁻¹ := by rw [hleft]
    _ = G⁻¹ - G⁻¹ * U * (⅟(⅟C + V * ⅟G * U)) * V * G⁻¹ := hwbN
    _ = G⁻¹ + G⁻¹ * U * A⁻¹ * V * G⁻¹ := by
      have hbridge' : ⅟C + V * ⅟G * U = -A := by
        simpa [invOf_eq_nonsing_inv] using hbridge
      have hmid : ⅟(⅟C + V * ⅟G * U) = -A⁻¹ := by
        calc
          ⅟(⅟C + V * ⅟G * U) =
              (⅟C + V * ⅟G * U)⁻¹ := by
                rw [invOf_eq_nonsing_inv]
          _ = (-A)⁻¹ := by rw [hbridge']
          _ = -A⁻¹ := nonsingInv_neg_of_invertible A
      rw [hmid]
      simp only [sub_eq_add_neg, Matrix.mul_assoc]
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_neg]
      exact congrArg (fun M : Matrix p p ℝ => G⁻¹ + M)
        (neg_neg (G⁻¹ * (U * (A⁻¹ * (V * G⁻¹)))))

private theorem dual_schur_sub_nonsingInv_invertible_of_primal
    (G : Matrix p p ℝ) (U : Matrix p q ℝ) (S A : Matrix q q ℝ) (V : Matrix q p ℝ)
    [Invertible G] [Invertible S] [Invertible A]
    (hA : A = S - V * G⁻¹ * U) :
    Nonempty (Invertible (G - U * S⁻¹ * V)) := by
  classical
  have hA' : S - V * ⅟G * U = A := by
    rw [invOf_eq_nonsing_inv]
    exact hA.symm
  letI : Invertible (S - V * ⅟G * U) :=
    Invertible.copy (inferInstance : Invertible A) _ hA'
  letI : Invertible (Matrix.fromBlocks S V U G) :=
    Matrix.fromBlocks₂₂Invertible S V U G
  letI : Invertible (G - U * ⅟S * V) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible S V U G
  exact ⟨Invertible.copy
    (inferInstance : Invertible (G - U * ⅟S * V))
    (G - U * S⁻¹ * V)
    (by rw [invOf_eq_nonsing_inv])⟩

end MatrixWoodburyHelpers

/-- Numerator of Hansen's Sargan statistic, `ê' P_Z ê`, using the totalized
2SLS residual and instrument projection. -/
noncomputable def twoSLSSarganNumeratorStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  let ehat := twoSLSResidualStar Z X Y
  ehat ⬝ᵥ (instrumentProjectionStar Z *ᵥ ehat)

/-- Unnormalized residual instrument score `Z' ê` for Hansen's Sargan
statistic.  This is the finite-sample score whose quadratic form is exactly
`ê' P_Z ê`. -/
noncomputable def twoSLSSarganResidualScoreStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) : l → ℝ :=
  Zᵀ *ᵥ twoSLSResidualStar Z X Y

/-- Scaled residual instrument-score measurability from row measurability.
This discharges the finite-sample measurability side condition used by the
Hansen Theorem 12.16 Sargan CLT wrappers. -/
theorem twoSLSSarganResidualScoreStar_scaled_aemeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (m : ℕ) :
    AEMeasurable
      (fun ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (fun i : Fin m => Z i.val ω) (fun i : Fin m => X i.val ω)
            (fun i : Fin m => Y i.val ω)) μ := by
  let Zmat : Ω → Matrix (Fin m) l ℝ := fun ω => fun i => Z i.val ω
  have hZmat : AEStronglyMeasurable Zmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) (X := Z) hZ
  have hZt : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZmat
  have hres : AEStronglyMeasurable
      (fun ω =>
        twoSLSResidualStar
          (fun i : Fin m => Z i.val ω) (fun i : Fin m => X i.val ω)
          (fun i : Fin m => Y i.val ω)) μ :=
    twoSLSResidualStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hscore : AEStronglyMeasurable
      (fun ω =>
        (Zmat ω)ᵀ *ᵥ
          twoSLSResidualStar
            (fun i : Fin m => Z i.val ω) (fun i : Fin m => X i.val ω)
            (fun i : Fin m => Y i.val ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZt.prodMk hres)
  simpa [twoSLSSarganResidualScoreStar, Zmat] using
    (hscore.const_smul ((Real.sqrt (m : ℝ))⁻¹)).aemeasurable

/-- Score-quadratic form equal to Hansen's Sargan numerator. -/
noncomputable def twoSLSSarganScoreQuadraticStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  let g := twoSLSSarganResidualScoreStar Z X Y
  g ⬝ᵥ ((Zᵀ * Z)⁻¹ *ᵥ g)

/-- Hansen Sargan statistic (12.67),
`S = ê' Z (Z'Z)^{-1} Z' ê / σ̂²`.  Division is Lean's totalized real division,
so the statistic is `0` on a zero residual-variance denominator. -/
noncomputable def twoSLSSarganStatOrZero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  twoSLSSarganNumeratorStar Z X Y / twoSLSSigmaSqHatStar Z X Y

/-- Hansen Sargan statistic written as the residual-score quadratic form divided
by the same totalized residual variance. -/
noncomputable def twoSLSSarganScoreStatOrZero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  twoSLSSarganScoreQuadraticStar Z X Y / twoSLSSigmaSqHatStar Z X Y

/-- Finite-sample Sargan numerator measurability from row measurability. -/
theorem twoSLSSarganNumeratorStar_aestronglyMeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSSarganNumeratorStar
          (fun i : Fin m => Z i.val ω) (fun i : Fin m => X i.val ω)
          (fun i : Fin m => Y i.val ω)) μ := by
  let Zmat : Ω → Matrix (Fin m) l ℝ := fun ω => fun i => Z i.val ω
  let res : Ω → Fin m → ℝ := fun ω =>
    twoSLSResidualStar (fun i : Fin m => Z i.val ω)
      (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)
  have hZmat : AEStronglyMeasurable Zmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) (X := Z) hZ
  have hZt : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZmat
  have hZZ : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ * Zmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZt.prodMk hZmat)
  have hZZinv : AEStronglyMeasurable (fun ω => ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hZZ
  have hPleft :
      AEStronglyMeasurable (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZmat.prodMk hZZinv)
  have hP : AEStronglyMeasurable
      (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hPleft.prodMk hZt)
  have hres : AEStronglyMeasurable res μ :=
    twoSLSResidualStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hPRes : AEStronglyMeasurable
      (fun ω => (Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) *ᵥ
        res ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hP.prodMk hres)
  have hnum : AEStronglyMeasurable
      (fun ω => res ω ⬝ᵥ
        ((Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) *ᵥ
          res ω)) μ :=
    (Continuous.dotProduct continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hres.prodMk hPRes)
  simpa [twoSLSSarganNumeratorStar, instrumentProjectionStar, Zmat, res,
    Matrix.mul_assoc] using hnum

/-- Finite-sample Sargan statistic measurability from row measurability. -/
theorem twoSLSSarganStatOrZero_aemeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEMeasurable
      (fun ω =>
        twoSLSSarganStatOrZero
          (fun i : Fin m => Z i.val ω) (fun i : Fin m => X i.val ω)
          (fun i : Fin m => Y i.val ω)) μ := by
  have hnum :=
    twoSLSSarganNumeratorStar_aestronglyMeasurable_of_rows
      (μ := μ) (m := m) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hsigma :=
    twoSLSSigmaSqHatStar_aestronglyMeasurable_of_rows
      (μ := μ) (n := m) (Z := Z) (X := X) (Y := Y) hZ hX hY
  simpa [twoSLSSarganStatOrZero] using hnum.aemeasurable.div hsigma.aemeasurable

omit [DecidableEq n] in
/-- Exact projection-to-score identity for the Sargan numerator:
`ê'P_Zê = (Z'ê)'(Z'Z)^{-1}(Z'ê)`.  This is the finite-sample algebraic bridge
behind the Wald/score representation of Hansen Theorem 12.16. -/
theorem twoSLSSarganNumeratorStar_eq_scoreQuadraticStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSSarganNumeratorStar Z X Y =
      twoSLSSarganScoreQuadraticStar Z X Y := by
  unfold twoSLSSarganNumeratorStar twoSLSSarganScoreQuadraticStar
    twoSLSSarganResidualScoreStar instrumentProjectionStar
  simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.dotProduct_mulVec,
    vecMul_eq_mulVec_transpose]

omit [DecidableEq n] in
/-- Exact statistic-level form of
`twoSLSSarganNumeratorStar_eq_scoreQuadraticStar`. -/
theorem twoSLSSarganStatOrZero_eq_scoreStatOrZero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSSarganStatOrZero Z X Y =
      twoSLSSarganScoreStatOrZero Z X Y := by
  simp [twoSLSSarganStatOrZero, twoSLSSarganScoreStatOrZero,
    twoSLSSarganNumeratorStar_eq_scoreQuadraticStar]

omit [DecidableEq n] in
/-- Hansen's score-form Sargan statistic is the Chapter 9 criterion statistic
for the normalized residual score `n^{-1/2} Z'ê` and covariance estimate
`σ̂² Q̂_ZZ`.  This deterministic bridge lets Theorem 12.16 reuse the generic
criterion-statistic CMT layer instead of assuming the final Sargan limit. -/
theorem twoSLSSarganScoreStatOrZero_eq_criterionJStatOrZero_scaledScore
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSSarganScoreStatOrZero Z X Y =
      criterionJStatOrZero
        ((Real.sqrt (Fintype.card n : ℝ))⁻¹ • twoSLSSarganResidualScoreStar Z X Y)
        (twoSLSSigmaSqHatStar Z X Y • sampleQZZ Z) := by
  let N : ℝ := Fintype.card n
  let rootInv : ℝ := (Real.sqrt N)⁻¹
  let g : l → ℝ := twoSLSSarganResidualScoreStar Z X Y
  let sigma : ℝ := twoSLSSigmaSqHatStar Z X Y
  by_cases hn0 : Fintype.card n = 0
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn0
    simp [twoSLSSarganScoreStatOrZero, twoSLSSarganScoreQuadraticStar,
      twoSLSSarganResidualScoreStar, twoSLSSigmaSqHatStar,
      sampleErrorSecondMoment, sampleQZZ, sampleGram, criterionJStatOrZero]
  haveI : Nonempty n :=
    Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  have hN_pos : 0 < N := by
    simpa [N] using
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card n) :
        0 < (Fintype.card n : ℝ))
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hQinv : (sampleQZZ Z)⁻¹ = N • (Zᵀ * Z)⁻¹ := by
    dsimp [sampleQZZ, sampleGram, N]
    rw [nonsingInv_smul]
    simp
  have hroot_sq : rootInv * rootInv * N = 1 := by
    have hsqrt_ne : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN_pos)
    dsimp [rootInv]
    field_simp [hsqrt_ne, hN_ne]
    rw [Real.sq_sqrt hN_pos.le]
  have hscale : rootInv * (sigma⁻¹ * (N * rootInv)) = sigma⁻¹ := by
    calc
      rootInv * (sigma⁻¹ * (N * rootInv))
          = sigma⁻¹ * (rootInv * rootInv * N) := by ring
      _ = sigma⁻¹ := by rw [hroot_sq, mul_one]
  have hcrit :
      criterionJStatOrZero (rootInv • g) (sigma • sampleQZZ Z) =
        (g ⬝ᵥ ((Zᵀ * Z)⁻¹ *ᵥ g)) / sigma := by
    rw [criterionJStatOrZero, nonsingInv_smul, hQinv]
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    rw [dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    change rootInv * (sigma⁻¹ * N) * (rootInv *
        (g ⬝ᵥ ((Zᵀ * Z)⁻¹ *ᵥ g))) =
      (g ⬝ᵥ ((Zᵀ * Z)⁻¹ *ᵥ g)) / sigma
    rw [show rootInv * (sigma⁻¹ * N) *
        (rootInv * (g ⬝ᵥ ((Zᵀ * Z)⁻¹ *ᵥ g))) =
        rootInv * (sigma⁻¹ * (N * rootInv)) *
          (g ⬝ᵥ ((Zᵀ * Z)⁻¹ *ᵥ g)) by ring]
    rw [hscale]
    ring
  calc
    twoSLSSarganScoreStatOrZero Z X Y
        = (g ⬝ᵥ ((Zᵀ * Z)⁻¹ *ᵥ g)) / sigma := by
            rfl
    _ = criterionJStatOrZero (rootInv • g) (sigma • sampleQZZ Z) := hcrit.symm

/-- Sample residual-maker in the instrument-score space appearing in Hansen's
proof of Theorem 12.16.  In the normalized `Q_ZZ = I` case this is
`I_l - Q (Q'Q)^{-1} Q'`. -/
noncomputable def twoSLSOveridResidualMaker
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix l l ℝ :=
  (1 : Matrix l l ℝ) -
    sampleQZX Z X *
      (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X))⁻¹ *
      sampleQXZ Z X * (sampleQZZ Z)⁻¹

/-- Population residual-maker in the instrument-score space for Hansen's
Sargan overidentification argument. -/
noncomputable def twoSLSOveridPopulationResidualMaker
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ) :
    Matrix l l ℝ :=
  (1 : Matrix l l ℝ) -
    QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹

/-- Matrix of the limiting quadratic form after the population residual-maker
has been applied to the instrument-error score. -/
noncomputable def twoSLSOveridLimitCriterionMatrix
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ)
    (sigma2 : ℝ) : Matrix l l ℝ :=
  let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  Mᵀ * (sigma2 • QZZ)⁻¹ * M

/-- Pullback of the Sargan limiting quadratic form through a square Gaussian
factor `B` for the instrument-error score covariance. -/
noncomputable def twoSLSOveridLimitCriterionPullback
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ)
    (sigma2 : ℝ) (B : Matrix l l ℝ) : Matrix l l ℝ :=
  Bᵀ * twoSLSOveridLimitCriterionMatrix QXZ QZZ QZX sigma2 * B

/-- The population residual-maker is idempotent whenever the 2SLS population
bread is nonsingular. This is the deterministic projection algebra behind
Hansen Theorem 12.16. -/
theorem twoSLSOveridPopulationResidualMaker_idempotent
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hB : IsUnit (twoSLSBread QXZ QZZ QZX).det) :
    IsIdempotentElem (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX) := by
  let H : Matrix k k ℝ := twoSLSBread QXZ QZZ QZX
  let R : Matrix l l ℝ := QZX * H⁻¹ * QXZ * QZZ⁻¹
  have hR : R * R = R := by
    dsimp [R, H, twoSLSBread]
    calc
      (QZX * (QXZ * QZZ⁻¹ * QZX)⁻¹ * QXZ * QZZ⁻¹) *
          (QZX * (QXZ * QZZ⁻¹ * QZX)⁻¹ * QXZ * QZZ⁻¹)
          =
          QZX * (QXZ * QZZ⁻¹ * QZX)⁻¹ *
            (QXZ * QZZ⁻¹ * QZX) *
              ((QXZ * QZZ⁻¹ * QZX)⁻¹ * QXZ * QZZ⁻¹) := by
            simp [Matrix.mul_assoc]
      _ =
          (QZX * ((QXZ * QZZ⁻¹ * QZX)⁻¹ *
            (QXZ * QZZ⁻¹ * QZX))) *
            ((QXZ * QZZ⁻¹ * QZX)⁻¹ * QXZ * QZZ⁻¹) := by
            simp [Matrix.mul_assoc]
      _ =
          (QZX * (1 : Matrix k k ℝ)) *
            ((QXZ * QZZ⁻¹ * QZX)⁻¹ * QXZ * QZZ⁻¹) := by
            rw [Matrix.nonsing_inv_mul (QXZ * QZZ⁻¹ * QZX)
              (by simpa [twoSLSBread, Matrix.mul_assoc] using hB)]
      _ = QZX * (QXZ * QZZ⁻¹ * QZX)⁻¹ * QXZ * QZZ⁻¹ := by
            simp [Matrix.mul_assoc]
  unfold IsIdempotentElem twoSLSOveridPopulationResidualMaker
  change (1 - R) * (1 - R) = 1 - R
  calc
    (1 - R) * (1 - R) = 1 - R - (R - R * R) := by
      rw [sub_mul, one_mul, mul_sub, mul_one]
    _ = 1 - R := by simp [hR]

/-- The trace of the population residual-maker is the overidentifying degrees
of freedom `ℓ - k`. This is the population analogue of Hansen's projection
rank calculation in Theorem 12.16. -/
theorem twoSLSOveridPopulationResidualMaker_trace
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hB : IsUnit (twoSLSBread QXZ QZZ QZX).det) :
    Matrix.trace (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX) =
      (Fintype.card l : ℝ) - Fintype.card k := by
  let H : Matrix k k ℝ := twoSLSBread QXZ QZZ QZX
  have htraceR :
      Matrix.trace (QZX * H⁻¹ * QXZ * QZZ⁻¹) = (Fintype.card k : ℝ) := by
    calc
      Matrix.trace (QZX * H⁻¹ * QXZ * QZZ⁻¹)
          = Matrix.trace ((QZX * H⁻¹) * (QXZ * QZZ⁻¹)) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace ((QXZ * QZZ⁻¹) * (QZX * H⁻¹)) := by
            rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (H * H⁻¹) := by
            simp [H, twoSLSBread, Matrix.mul_assoc]
      _ = Matrix.trace (1 : Matrix k k ℝ) := by
            rw [Matrix.mul_nonsing_inv H (by simpa [H] using hB)]
      _ = (Fintype.card k : ℝ) := by rw [Matrix.trace_one]
  dsimp [twoSLSOveridPopulationResidualMaker, H]
  rw [Matrix.trace_sub, Matrix.trace_one, htraceR]

/-- Weighted self-adjointness of the population residual-maker:
`M Q_ZZ = Q_ZZ M'`. This is Hansen's oblique projection written in the
`Q_ZZ` inner product. -/
theorem twoSLSOveridPopulationResidualMaker_weighted_selfAdjoint
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hQXZ : QXZ = QZXᵀ) (hQZZsymm : QZZᵀ = QZZ)
    (hQZZ : IsUnit QZZ.det) :
    let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
    M * QZZ = QZZ * Mᵀ := by
  intro M
  let H : Matrix k k ℝ := twoSLSBread QXZ QZZ QZX
  have hQZZinv : (QZZ⁻¹)ᵀ = QZZ⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hQZZsymm]
  have hQXZ_t : QXZᵀ = QZX := by
    rw [hQXZ, Matrix.transpose_transpose]
  have hQZX_t : QZXᵀ = QXZ := hQXZ.symm
  have hHsymm : Hᵀ = H := by
    simpa [H] using
      twoSLSBread_transpose_of_qzz_symm
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) hQXZ hQZZsymm
  have hHinv_symm : (H⁻¹)ᵀ = H⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hHsymm]
  have hbreadInv_symm :
      ((twoSLSBread QXZ QZZ QZX)⁻¹)ᵀ =
        (twoSLSBread QXZ QZZ QZX)⁻¹ := by
    simpa [H] using hHinv_symm
  dsimp [M, twoSLSOveridPopulationResidualMaker, H]
  calc
    ((1 : Matrix l l ℝ) -
        QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) * QZZ
        = QZZ - QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ := by
          rw [sub_mul, one_mul]
          simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQZZ]
    _ = QZZ *
        ((1 : Matrix l l ℝ) -
          QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹)ᵀ := by
          symm
          rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
            Matrix.transpose_mul, Matrix.transpose_mul, hQZZinv]
          rw [Matrix.mul_sub, Matrix.mul_one]
          simp only [hQXZ_t, hQZX_t, hbreadInv_symm, Matrix.mul_assoc, sub_right_inj]
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv QZZ hQZZ, Matrix.one_mul]

/-- The limiting Sargan quadratic-form pullback is Hermitian whenever the
homoskedastic score covariance `σ² Q_ZZ` is positive definite. -/
theorem twoSLSOveridLimitCriterionPullback_isHermitian
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} (B : Matrix l l ℝ)
    (hV : (sigma2 • QZZ).PosDef) :
    (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B).IsHermitian := by
  let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let V := sigma2 • QZZ
  have hA : (twoSLSOveridLimitCriterionMatrix QXZ QZZ QZX sigma2).IsHermitian := by
    simpa [twoSLSOveridLimitCriterionMatrix, M, V,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul M hV.inv.isHermitian
  simpa [twoSLSOveridLimitCriterionPullback,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul B hA

/-- With the CFC square root `S = sqrt(σ² Q_ZZ)`, the Sargan limit pullback is
similar to the population residual-maker, `S⁻¹ M S`. This is the reusable
whitening identity behind the idempotence, trace, and rank calculations for
Hansen Theorem 12.16. -/
theorem twoSLSOveridLimitCriterionPullback_eq_whitenedResidualMaker_of_weightedSelfAdjoint
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ}
    (hV : (sigma2 • QZZ).PosDef)
    (hMidem : IsIdempotentElem
      (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX))
    (hMself :
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      M * (sigma2 • QZZ) = (sigma2 • QZZ) * Mᵀ) :
    twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2
        (CFC.sqrt (sigma2 • QZZ)) =
      (CFC.sqrt (sigma2 • QZZ))⁻¹ *
        twoSLSOveridPopulationResidualMaker QXZ QZZ QZX *
          CFC.sqrt (sigma2 • QZZ) := by
  let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let V := sigma2 • QZZ
  let S : Matrix l l ℝ := CFC.sqrt V
  have hVunit : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit
  have hSunit : IsUnit S.det := by
    have hS : S.PosDef := by simpa [S] using hV.isStrictlyPositive.sqrt.posDef
    exact (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hSS : S * S = V := by
    simpa [S] using CFC.sqrt_mul_sqrt_self V hV.posSemidef.nonneg
  have hS_trans : Sᵀ = S := by
    have hS : S.PosDef := by simpa [S] using hV.isStrictlyPositive.sqrt.posDef
    have hHerm : S.IsHermitian := hS.1
    simpa [Matrix.conjTranspose] using hHerm.eq
  have hMV : M * V = V * Mᵀ := by
    simpa [M, V] using hMself
  have hMtVinv : Mᵀ * V⁻¹ = V⁻¹ * M := by
    calc
      Mᵀ * V⁻¹ = (1 : Matrix l l ℝ) * (Mᵀ * V⁻¹) := by simp
      _ = (V⁻¹ * V) * (Mᵀ * V⁻¹) := by
        rw [Matrix.nonsing_inv_mul V hVunit]
      _ = V⁻¹ * (V * Mᵀ) * V⁻¹ := by simp [Matrix.mul_assoc]
      _ = V⁻¹ * (M * V) * V⁻¹ := by rw [← hMV]
      _ = V⁻¹ * M * (V * V⁻¹) := by simp [Matrix.mul_assoc]
      _ = V⁻¹ * M * 1 := by rw [Matrix.mul_nonsing_inv V hVunit]
      _ = V⁻¹ * M := by simp
  have hMM : M * M = M := by
    simpa [IsIdempotentElem, M] using hMidem
  have hLimit :
      twoSLSOveridLimitCriterionMatrix QXZ QZZ QZX sigma2 = V⁻¹ * M := by
    dsimp [twoSLSOveridLimitCriterionMatrix, M, V]
    rw [hMtVinv, Matrix.mul_assoc, hMM]
  have hSVinv : S * V⁻¹ = S⁻¹ := by
    calc
      S * V⁻¹ = S * (S * S)⁻¹ := by rw [hSS]
      _ = S * (S⁻¹ * S⁻¹) := by rw [Matrix.mul_inv_rev]
      _ = (S * S⁻¹) * S⁻¹ := by simp [Matrix.mul_assoc]
      _ = (1 : Matrix l l ℝ) * S⁻¹ := by
        rw [Matrix.mul_nonsing_inv S hSunit]
      _ = S⁻¹ := by simp
  have hP :
      twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 S =
        S⁻¹ * M * S := by
    dsimp [twoSLSOveridLimitCriterionPullback]
    rw [hLimit, hS_trans]
    rw [← Matrix.mul_assoc S V⁻¹ M, hSVinv]
  simpa [M, V, S] using hP

/-- Whitening an idempotent residual-maker that is self-adjoint in the
`σ² Q_ZZ` inner product gives an ordinary idempotent pullback. -/
theorem twoSLSOveridLimitCriterionPullback_idempotent_of_weightedSelfAdjoint
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ}
    (hV : (sigma2 • QZZ).PosDef)
    (hMidem : IsIdempotentElem
      (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX))
    (hMself :
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      M * (sigma2 • QZZ) = (sigma2 • QZZ) * Mᵀ) :
    IsIdempotentElem
      (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2
        (CFC.sqrt (sigma2 • QZZ))) := by
  let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let V := sigma2 • QZZ
  let S : Matrix l l ℝ := CFC.sqrt V
  have hSunit : IsUnit S.det := by
    have hS : S.PosDef := by simpa [S] using hV.isStrictlyPositive.sqrt.posDef
    exact (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hMM : M * M = M := by
    simpa [IsIdempotentElem, M] using hMidem
  have hP :
      twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 S =
        S⁻¹ * M * S := by
    simpa [M, V, S] using
      twoSLSOveridLimitCriterionPullback_eq_whitenedResidualMaker_of_weightedSelfAdjoint
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2)
        hV hMidem hMself
  rw [show CFC.sqrt (sigma2 • QZZ) = S by rfl]
  rw [hP]
  unfold IsIdempotentElem
  calc
    (S⁻¹ * M * S) * (S⁻¹ * M * S)
        = S⁻¹ * M * (S * S⁻¹) * M * S := by simp [Matrix.mul_assoc]
    _ = S⁻¹ * M * (1 : Matrix l l ℝ) * M * S := by
        rw [Matrix.mul_nonsing_inv S hSunit]
    _ = S⁻¹ * (M * M) * S := by simp [Matrix.mul_assoc]
    _ = S⁻¹ * M * S := by rw [hMM]

/-- The whitened Sargan pullback has the same trace as the population
residual-maker. -/
theorem twoSLSOveridLimitCriterionPullback_trace_of_weightedSelfAdjoint
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ}
    (hV : (sigma2 • QZZ).PosDef)
    (hMidem : IsIdempotentElem
      (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX))
    (hMself :
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      M * (sigma2 • QZZ) = (sigma2 • QZZ) * Mᵀ) :
    Matrix.trace
        (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2
          (CFC.sqrt (sigma2 • QZZ))) =
      Matrix.trace (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX) := by
  let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let V := sigma2 • QZZ
  let S : Matrix l l ℝ := CFC.sqrt V
  have hSunit : IsUnit S.det := by
    have hS : S.PosDef := by simpa [S] using hV.isStrictlyPositive.sqrt.posDef
    exact (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hP :
      twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 S =
        S⁻¹ * M * S := by
    simpa [M, V, S] using
      twoSLSOveridLimitCriterionPullback_eq_whitenedResidualMaker_of_weightedSelfAdjoint
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2)
        hV hMidem hMself
  rw [show CFC.sqrt (sigma2 • QZZ) = S by rfl, hP]
  calc
    Matrix.trace (S⁻¹ * M * S)
        = Matrix.trace (S * S⁻¹ * M) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace ((S * S⁻¹) * M) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace (1 * M) := by rw [Matrix.mul_nonsing_inv S hSunit]
    _ = Matrix.trace M := by simp

/-- Rank of the whitened population residual-maker in Hansen Theorem 12.16:
under the population rank and homoskedastic positive-definiteness assumptions,
the CFC-whitened pullback has rank exactly `ℓ - k`. -/
theorem twoSLSOveridLimitCriterionPullback_rank_sqrtCov
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ_pos : QZZ.PosDef)
    (hQZX_rank : Function.Injective QZX.mulVec)
    (hsigma_pos : 0 < sigma2) :
    (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2
        (CFC.sqrt (sigma2 • QZZ))).rank =
      Fintype.card l - Fintype.card k := by
  let B : Matrix l l ℝ := CFC.sqrt (sigma2 • QZZ)
  have hV : (sigma2 • QZZ).PosDef := hQZZ_pos.smul hsigma_pos
  have hH : (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B).IsHermitian :=
    twoSLSOveridLimitCriterionPullback_isHermitian
      (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2) B hV
  have hQZZ_symm : QZZᵀ = QZZ := by
    have hHerm : QZZ.IsHermitian := hQZZ_pos.isHermitian
    simpa [Matrix.conjTranspose] using hHerm.eq
  have hQZZ_unit : IsUnit QZZ.det := (Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ_pos.isUnit
  have hBread_unit : IsUnit (twoSLSBread QXZ QZZ QZX).det :=
    isUnit_twoSLSBread_det_of_qzz_posDef_rank hQXZ hQZZ_pos hQZX_rank
  have hMidem : IsIdempotentElem
      (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX) :=
    twoSLSOveridPopulationResidualMaker_idempotent hBread_unit
  have hMselfQ :
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      M * QZZ = QZZ * Mᵀ :=
    twoSLSOveridPopulationResidualMaker_weighted_selfAdjoint
      hQXZ hQZZ_symm hQZZ_unit
  have hMselfV :
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      M * (sigma2 • QZZ) = (sigma2 • QZZ) * Mᵀ := by
    dsimp
    simpa [Matrix.mul_smul, Matrix.smul_mul] using
      congrArg (fun A : Matrix l l ℝ => sigma2 • A) hMselfQ
  have hI : IsIdempotentElem
      (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B) := by
    simpa [B] using
      twoSLSOveridLimitCriterionPullback_idempotent_of_weightedSelfAdjoint
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2)
        hV hMidem hMselfV
  have hRankTrace := rank_eq_natCast_trace_of_isHermitian_idempotent hH hI
  have hPullTrace :
      Matrix.trace (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B) =
        Matrix.trace (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX) := by
    simpa [B] using
      twoSLSOveridLimitCriterionPullback_trace_of_weightedSelfAdjoint
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2)
        hV hMidem hMselfV
  rw [hPullTrace, twoSLSOveridPopulationResidualMaker_trace hBread_unit] at hRankTrace
  have hle : Fintype.card k ≤ Fintype.card l :=
    Nat.le_of_lt (Nat.lt_of_sub_pos Fact.out)
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_sub hle]
  simpa [B] using hRankTrace

set_option maxHeartbeats 2000000 in
-- The sample-moment package has several dependent matrix fields, making
-- elaboration of the residual-maker expression expensive.
/-- Residual-maker measurability from Hansen's sample IV moment package. -/
theorem twoSLSOveridResidualMaker_aestronglyMeasurable_of_sample_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX) :
    ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSOveridResidualMaker
          (stackRegressors Z n ω) (stackRegressors X n ω)) μ := by
  intro n
  let QXZhat : Ω → Matrix k l ℝ := fun ω =>
    sampleQXZ (stackRegressors Z n ω) (stackRegressors X n ω)
  let QZZhat : Ω → Matrix l l ℝ := fun ω =>
    sampleQZZ (stackRegressors Z n ω)
  let QZXhat : Ω → Matrix l k ℝ := fun ω =>
    sampleQZX (stackRegressors Z n ω) (stackRegressors X n ω)
  have hQXZ : AEStronglyMeasurable QXZhat μ := by
    simpa [QXZhat] using h.qxz_meas n
  have hQZZ : AEStronglyMeasurable QZZhat μ := by
    simpa [QZZhat] using h.qzz_meas n
  have hQZX : AEStronglyMeasurable QZXhat μ := by
    simpa [QZXhat] using h.qzx_meas n
  have hQZZinv : AEStronglyMeasurable (fun ω => (QZZhat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hQZZ
  have hbread_left : AEStronglyMeasurable (fun ω => QXZhat ω * (QZZhat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQXZ.prodMk hQZZinv)
  have hbread : AEStronglyMeasurable
      (fun ω => twoSLSBread (QXZhat ω) (QZZhat ω) (QZXhat ω)) μ := by
    have hraw : AEStronglyMeasurable
        (fun ω => (QXZhat ω * (QZZhat ω)⁻¹) * QZXhat ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hbread_left.prodMk hQZX)
    simpa [twoSLSBread, Matrix.mul_assoc] using hraw
  have hbreadInv : AEStronglyMeasurable
      (fun ω => (twoSLSBread (QXZhat ω) (QZZhat ω) (QZXhat ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hbread
  have hterm1 : AEStronglyMeasurable
      (fun ω => QZXhat ω *
        (twoSLSBread (QXZhat ω) (QZZhat ω) (QZXhat ω))⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQZX.prodMk hbreadInv)
  have hterm2 : AEStronglyMeasurable
      (fun ω => QZXhat ω *
        (twoSLSBread (QXZhat ω) (QZZhat ω) (QZXhat ω))⁻¹ * QXZhat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hterm1.prodMk hQXZ)
  have hterm : AEStronglyMeasurable
      (fun ω => QZXhat ω *
        (twoSLSBread (QXZhat ω) (QZZhat ω) (QZXhat ω))⁻¹ *
        QXZhat ω * (QZZhat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hterm2.prodMk hQZZinv)
  have hone : AEStronglyMeasurable
      (fun _ : Ω => (1 : Matrix l l ℝ)) μ :=
    aestronglyMeasurable_const
  have hmaker := hone.sub hterm
  simpa [twoSLSOveridResidualMaker, QXZhat, QZZhat, QZXhat, Matrix.mul_assoc] using
    hmaker

set_option maxHeartbeats 2000000 in
-- Matrix-product CMT synthesis is expensive for the four-factor rectangular expression below.
/-- Residual-maker CMT from Hansen's sample IV moment limits.

This is the deterministic continuous-mapping part of the Sargan projection
argument: the sample matrix
`I - Q̂_ZX (Q̂_XZ Q̂_ZZ⁻¹ Q̂_ZX)⁻¹ Q̂_XZ Q̂_ZZ⁻¹` converges to its population
counterpart. The theorem reuses the Chapter 12 sample-moment package and the
previously proved 2SLS bread CMT. -/
theorem twoSLSOveridResidualMaker_tendstoInMeasure_of_sample_moments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSOveridResidualMaker
          (stackRegressors Z n ω) (stackRegressors X n ω))
      atTop
      (fun _ =>
        (1 : Matrix l l ℝ) -
          QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) := by
  let QXZhat : ℕ → Ω → Matrix k l ℝ := fun n ω =>
    sampleQXZ (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let QZZhat : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    sampleQZZ (fun i : Fin n => Z i.val ω)
  let QZXhat : ℕ → Ω → Matrix l k ℝ := fun n ω =>
    sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  have hQZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (QZZhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.qzz_meas n)
  have hQZZinv : TendstoInMeasure μ
      (fun n ω => (QZZhat n ω)⁻¹) atTop (fun _ => QZZ⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) h.qzz_meas h.qzz_tendsto
      (fun _ => h.qzz_nonsing)
  have hQXZ_QZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((h.qxz_meas n).prodMk (hQZZinv_meas n))
  have hQXZ_QZZinv : TendstoInMeasure μ
      (fun n ω => QXZhat n ω * (QZZhat n ω)⁻¹)
      atTop (fun _ => QXZ * QZZ⁻¹) :=
    tendstoInMeasure_matrix_mul_rect h.qxz_meas hQZZinv_meas
      h.qxz_tendsto hQZZinv
  have hbread_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQXZ_QZZinv_meas n).prodMk (h.qzx_meas n))
  have hbread : TendstoInMeasure μ
      (fun n ω => QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω)
      atTop (fun _ => twoSLSBread QXZ QZZ QZX) := by
    simpa [twoSLSBread, Matrix.mul_assoc] using
      tendstoInMeasure_matrix_mul_rect hQXZ_QZZinv_meas h.qzx_meas
        hQXZ_QZZinv h.qzx_tendsto
  have hbread_folded_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω)) μ := by
    intro n
    simpa [twoSLSBread, Matrix.mul_assoc] using hbread_meas n
  have hbread_folded : TendstoInMeasure μ
      (fun n ω => twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))
      atTop (fun _ => twoSLSBread QXZ QZZ QZX) := by
    simpa [twoSLSBread, Matrix.mul_assoc] using hbread
  have hbreadInv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hbread_folded_meas n)
  have hbreadInv : TendstoInMeasure μ
      (fun n ω => (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹)
      atTop (fun _ => (twoSLSBread QXZ QZZ QZX)⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hbread_folded_meas hbread_folded
      (fun _ => h.bread_nonsing)
  have hQZX_breadInv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => QZXhat n ω *
          (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((h.qzx_meas n).prodMk (hbreadInv_meas n))
  have hQZX_breadInv : TendstoInMeasure μ
      (fun n ω => QZXhat n ω *
        (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹)
      atTop (fun _ => QZX * (twoSLSBread QXZ QZZ QZX)⁻¹) :=
    tendstoInMeasure_matrix_mul_rect h.qzx_meas hbreadInv_meas
      h.qzx_tendsto hbreadInv
  have hQZX_breadInv_QXZ_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          (QZXhat n ω *
              (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) *
            QXZhat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQZX_breadInv_meas n).prodMk (h.qxz_meas n))
  have hQZX_breadInv_QXZ : TendstoInMeasure μ
      (fun n ω =>
        (QZXhat n ω *
            (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) *
          QXZhat n ω)
      atTop (fun _ => QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ) :=
    tendstoInMeasure_matrix_mul_rect hQZX_breadInv_meas h.qxz_meas
      hQZX_breadInv h.qxz_tendsto
  have hterm_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          ((QZXhat n ω *
                (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) *
              QXZhat n ω) * (QZZhat n ω)⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQZX_breadInv_QXZ_meas n).prodMk (hQZZinv_meas n))
  have hterm : TendstoInMeasure μ
      (fun n ω =>
        ((QZXhat n ω *
              (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) *
            QXZhat n ω) * (QZZhat n ω)⁻¹)
      atTop (fun _ => QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) :=
    tendstoInMeasure_matrix_mul_rect hQZX_breadInv_QXZ_meas hQZZinv_meas
      hQZX_breadInv_QXZ hQZZinv
  have hcont : Continuous
      (fun A : Matrix l l ℝ => (1 : Matrix l l ℝ) - A) :=
    continuous_const.sub continuous_id
  have hmaker : TendstoInMeasure μ
      (fun n ω =>
        (1 : Matrix l l ℝ) -
          ((QZXhat n ω *
                (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) *
              QXZhat n ω) * (QZZhat n ω)⁻¹)
      atTop
      (fun _ =>
        (1 : Matrix l l ℝ) -
          QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) :=
    tendstoInMeasure_continuous_comp hterm_meas hterm hcont
  simpa [twoSLSOveridResidualMaker, QXZhat, QZZhat, QZXhat, Matrix.mul_assoc] using hmaker

omit [DecidableEq n] in
/-- The overidentifying residual-maker removes the component of the raw
instrument-error score explained by the 2SLS linearized coefficient error. -/
theorem twoSLSOveridResidualMaker_mul_score_eq
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) [Nonempty n] :
    twoSLSOveridResidualMaker Z X *ᵥ (Zᵀ *ᵥ e) =
      Zᵀ *ᵥ e -
        Zᵀ *ᵥ (X *ᵥ (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e)) := by
  unfold twoSLSOveridResidualMaker twoSLSLinearizationMatrix
    sampleQZX sampleCrossMoment
  simp [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.smul_mul,
    Matrix.smul_mulVec, Matrix.mulVec_smul]

omit [DecidableEq n] in
/-- Residual-score expansion for Hansen's Sargan proof.

Under the structural model and nonsingular 2SLS bread, the finite-sample
residual instrument score is the overidentifying residual-maker applied to the
true instrument-error score.  This is the deterministic core of the
projection/rank argument used to prove the `χ²_{ℓ-k}` limit in Theorem 12.16. -/
theorem twoSLSSarganResidualScoreStar_linear_model_eq_overidResidualMaker
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSSarganResidualScoreStar Z X (X *ᵥ β + e) =
      twoSLSOveridResidualMaker Z X *ᵥ (Zᵀ *ᵥ e) := by
  have hres :=
    twoSLSResidualStar_linear_model_of_nonsingular
      (Z := Z) (X := X) (β := β) (e := e) (hunit := hunit)
  unfold twoSLSSarganResidualScoreStar
  rw [hres]
  rw [twoSLSOveridResidualMaker_mul_score_eq]
  simp [Matrix.mulVec_sub]

/-- Hansen's residual-maker instrument score in the proof of Theorem 12.16:
`M Z'e`, where `M = I - Q_ZX (Q_XZ Q_ZZ⁻¹ Q_ZX)⁻¹ Q_XZ Q_ZZ⁻¹`. -/
noncomputable def twoSLSOveridResidualMakerScoreStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) : l → ℝ :=
  twoSLSOveridResidualMaker Z X *ᵥ (Zᵀ *ᵥ e)

/-- Quadratic form of the residual-maker score used in Hansen's proof of the
Sargan `χ²_{ℓ-k}` limit. -/
noncomputable def twoSLSOveridResidualMakerScoreQuadraticStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) : ℝ :=
  let g := twoSLSOveridResidualMakerScoreStar Z X e
  g ⬝ᵥ ((Zᵀ * Z)⁻¹ *ᵥ g)

/-- Sargan statistic written with the true structural error and Hansen's
overidentifying residual-maker, retaining the feasible residual-variance
denominator from the structural model. -/
noncomputable def twoSLSOveridResidualMakerScoreStatOrZero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) : ℝ :=
  twoSLSOveridResidualMakerScoreQuadraticStar Z X e /
    twoSLSSigmaSqHatStar Z X (X *ᵥ β + e)

omit [DecidableEq n] in
/-- Under the structural model, the score-quadratic Sargan numerator is exactly
the residual-maker quadratic form in the true instrument-error score.

This is the finite-sample deterministic bridge used before the residual-score
projection/rank argument in Hansen Theorem 12.16. -/
theorem twoSLSSarganScoreQuadraticStar_linear_model_eq_overidResidualMakerScoreQuadraticStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSSarganScoreQuadraticStar Z X (X *ᵥ β + e) =
      twoSLSOveridResidualMakerScoreQuadraticStar Z X e := by
  unfold twoSLSSarganScoreQuadraticStar
    twoSLSOveridResidualMakerScoreQuadraticStar
    twoSLSOveridResidualMakerScoreStar
  rw [twoSLSSarganResidualScoreStar_linear_model_eq_overidResidualMaker
    Z X β e hunit]

omit [DecidableEq n] in
/-- Structural-model statistic-level version of
`twoSLSSarganScoreQuadraticStar_linear_model_eq_overidResidualMakerScoreQuadraticStar`. -/
theorem twoSLSSarganScoreStatOrZero_linear_model_eq_overidResidualMakerScoreStatOrZero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSSarganScoreStatOrZero Z X (X *ᵥ β + e) =
      twoSLSOveridResidualMakerScoreStatOrZero Z X β e := by
  unfold twoSLSSarganScoreStatOrZero twoSLSOveridResidualMakerScoreStatOrZero
  rw [twoSLSSarganScoreQuadraticStar_linear_model_eq_overidResidualMakerScoreQuadraticStar
    Z X β e hunit]

omit [DecidableEq n] in
/-- Under the structural model, Hansen's Sargan statistic is exactly the
overidentifying residual-maker score statistic. -/
theorem twoSLSSarganStatOrZero_linear_model_eq_overidResidualMakerScoreStatOrZero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSSarganStatOrZero Z X (X *ᵥ β + e) =
      twoSLSOveridResidualMakerScoreStatOrZero Z X β e := by
  rw [twoSLSSarganStatOrZero_eq_scoreStatOrZero]
  exact twoSLSSarganScoreStatOrZero_linear_model_eq_overidResidualMakerScoreStatOrZero
    Z X β e hunit

/-- Subset-overidentification residualized excluded instruments
`R = M_a Z_b`, using the Star projection for `P_a`. -/
noncomputable def twoSLSSubsetResidualizedInstrumentsStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) : Matrix n lb ℝ :=
  ((1 : Matrix n n ℝ) - instrumentProjectionStar Za) * Zb

omit [Fintype lb] [DecidableEq lb] in
/-- Residualized excluded-instrument matrix measurability from row
measurability. -/
theorem twoSLSSubsetResidualizedInstrumentsStar_aestronglyMeasurable_of_rows
    [Finite lb]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (m : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedInstrumentsStar
          (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)) μ := by
  letI : Fintype lb := Fintype.ofFinite lb
  let ZaMat : Ω → Matrix (Fin m) la ℝ := fun ω => fun i => Za i.val ω
  let ZbMat : Ω → Matrix (Fin m) lb ℝ := fun ω => fun i => Zb i.val ω
  have hZaMat : AEStronglyMeasurable ZaMat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) (X := Za) hZa
  have hZbMat : AEStronglyMeasurable ZbMat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) (X := Zb) hZb
  have hZaT : AEStronglyMeasurable (fun ω => (ZaMat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZaMat
  have hGram : AEStronglyMeasurable (fun ω => (ZaMat ω)ᵀ * ZaMat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZaT.prodMk hZaMat)
  have hInv : AEStronglyMeasurable (fun ω => ((ZaMat ω)ᵀ * ZaMat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hPleft : AEStronglyMeasurable
      (fun ω => ZaMat ω * ((ZaMat ω)ᵀ * ZaMat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZaMat.prodMk hInv)
  have hP : AEStronglyMeasurable
      (fun ω => ZaMat ω * ((ZaMat ω)ᵀ * ZaMat ω)⁻¹ * (ZaMat ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hPleft.prodMk hZaT)
  have hM : AEStronglyMeasurable
      (fun ω => (1 : Matrix (Fin m) (Fin m) ℝ) -
        ZaMat ω * ((ZaMat ω)ᵀ * ZaMat ω)⁻¹ * (ZaMat ω)ᵀ) μ :=
    aestronglyMeasurable_const.sub hP
  have hR : AEStronglyMeasurable
      (fun ω => ((1 : Matrix (Fin m) (Fin m) ℝ) -
        ZaMat ω * ((ZaMat ω)ᵀ * ZaMat ω)⁻¹ * (ZaMat ω)ᵀ) * ZbMat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hM.prodMk hZbMat)
  simpa [twoSLSSubsetResidualizedInstrumentsStar, instrumentProjectionStar,
    ZaMat, ZbMat, Matrix.mul_assoc] using hR

omit [Fintype lb] [DecidableEq lb] in
/-- On a nonsingular restricted-instrument Gram matrix, Newey's residualized
instrument block is exactly the Chapter 3 annihilator matrix applied to the
excluded instruments. -/
theorem twoSLSSubsetResidualizedInstrumentsStar_eq_annihilatorMatrix
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) [Invertible (Zaᵀ * Za)] :
    twoSLSSubsetResidualizedInstrumentsStar Za Zb =
      annihilatorMatrix Za * Zb := by
  simp [twoSLSSubsetResidualizedInstrumentsStar, annihilatorMatrix,
    instrumentProjectionStar_eq_projection, instrumentProjection_eq_hatMatrix]

omit [DecidableEq n] [Fintype la] [DecidableEq la] [Fintype lb] [DecidableEq lb] in
/-- Gram matrix of a partitioned instrument block, written as a block matrix.

This is the deterministic block algebra used before applying Mathlib's Schur
complement theorem to the residualized excluded-instrument Gram. -/
theorem fromCols_transpose_mul_self_eq_fromBlocks
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) :
    (Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb =
      Matrix.fromBlocks
        (Zaᵀ * Za) (Zaᵀ * Zb) (Zbᵀ * Za) (Zbᵀ * Zb) := by
  ext i j
  cases i with
  | inl a =>
      cases j with
      | inl b => simp [Matrix.mul_apply]
      | inr b => simp [Matrix.mul_apply]
  | inr a =>
      cases j with
      | inl b => simp [Matrix.mul_apply]
      | inr b => simp [Matrix.mul_apply]

omit [Fintype lb] [DecidableEq lb] in
/-- The residualized excluded-instrument Gram is the Schur complement of the
maintained-instrument block inside the full partitioned instrument Gram. -/
theorem residualizedInstrumentsGram_eq_schurComplement_fromCols
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) [Invertible (Zaᵀ * Za)] :
    (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb =
      Zbᵀ * Zb - Zbᵀ * Za * ⅟(Zaᵀ * Za) * (Zaᵀ * Zb) := by
  let M := annihilatorMatrix Za
  have hR : twoSLSSubsetResidualizedInstrumentsStar Za Zb = M * Zb := by
    simpa [M] using twoSLSSubsetResidualizedInstrumentsStar_eq_annihilatorMatrix Za Zb
  have hMT : Mᵀ = M := by
    simpa [M] using annihilatorMatrix_transpose Za
  have hMIdem : M * M = M := by
    simpa [M] using annihilatorMatrix_idempotent Za
  calc
    (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb =
        (M * Zb)ᵀ * (M * Zb) := by rw [hR]
    _ = Zbᵀ * M * Zb := by
        calc
          (M * Zb)ᵀ * (M * Zb) =
              Zbᵀ * M * (M * Zb) := by
                rw [Matrix.transpose_mul, hMT]
          _ = Zbᵀ * (M * M) * Zb := by
                simp [Matrix.mul_assoc]
          _ = Zbᵀ * M * Zb := by rw [hMIdem]
    _ = Zbᵀ * (((1 : Matrix n n ℝ) -
          Za * ⅟(Zaᵀ * Za) * Zaᵀ) * Zb) := by
        simp [M, annihilatorMatrix, hatMatrix, Matrix.mul_assoc]
    _ = Zbᵀ * Zb - Zbᵀ * Za * ⅟(Zaᵀ * Za) * (Zaᵀ * Zb) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
        simp [Matrix.mul_assoc]

/-- Nonsingularity of the full and maintained partitioned instrument Grams
implies nonsingularity of the residualized excluded-instrument Gram.

This removes a redundant finite-sample 12.17 branch: `R'R` is exactly the Schur
complement of `Z_a'Z_a` inside `[Z_a,Z_b]'[Z_a,Z_b]`. -/
theorem residualizedInstrumentsGram_invertible_of_fromCols_gram_invertible
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible (Zaᵀ * Za)]
    (hZ : Nonempty (Invertible
      ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb))) :
    Nonempty (Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)) := by
  classical
  rcases hZ with ⟨instZ⟩
  letI : Invertible
      ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb) := instZ
  have hFull :
      (Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb =
        Matrix.fromBlocks
          (Zaᵀ * Za) (Zaᵀ * Zb) (Zbᵀ * Za) (Zbᵀ * Zb) :=
    fromCols_transpose_mul_self_eq_fromBlocks Za Zb
  letI : Invertible
      (Matrix.fromBlocks
        (Zaᵀ * Za) (Zaᵀ * Zb) (Zbᵀ * Za) (Zbᵀ * Zb)) :=
    Invertible.copy
      (inferInstance : Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb))
      (Matrix.fromBlocks
        (Zaᵀ * Za) (Zaᵀ * Zb) (Zbᵀ * Za) (Zbᵀ * Zb)) hFull.symm
  letI : Invertible
      (Zbᵀ * Zb - Zbᵀ * Za * ⅟(Zaᵀ * Za) * (Zaᵀ * Zb)) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible
      (Zaᵀ * Za) (Zaᵀ * Zb) (Zbᵀ * Za) (Zbᵀ * Zb)
  exact ⟨Invertible.copy
    (inferInstance :
      Invertible (Zbᵀ * Zb - Zbᵀ * Za * ⅟(Zaᵀ * Za) * (Zaᵀ * Zb)))
    ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
      twoSLSSubsetResidualizedInstrumentsStar Za Zb)
    (residualizedInstrumentsGram_eq_schurComplement_fromCols Za Zb)⟩

omit [Fintype lb] [DecidableEq lb] in
/-- Residualized excluded instruments are orthogonal to the maintained
instrument block on the nonsingular restricted-instrument branch. -/
theorem transpose_mul_twoSLSSubsetResidualizedInstrumentsStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) [Invertible (Zaᵀ * Za)] :
    Zaᵀ * twoSLSSubsetResidualizedInstrumentsStar Za Zb = 0 := by
  have hMZa : annihilatorMatrix Za * Za = 0 := annihilator_mul_X Za
  have hleft : Zaᵀ * annihilatorMatrix Za = 0 := by
    have hT := congrArg Matrix.transpose hMZa
    simpa [Matrix.transpose_mul, annihilatorMatrix_transpose] using hT
  rw [twoSLSSubsetResidualizedInstrumentsStar_eq_annihilatorMatrix]
  rw [← Matrix.mul_assoc, hleft, Matrix.zero_mul]

/-- Hansen's `P_R`: projection onto the residualized excluded-instrument span
`R = M_a Z_b`, written with the totalized inverse. -/
noncomputable def twoSLSSubsetResidualizedProjectionStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) : Matrix n n ℝ :=
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  R * (Rᵀ * R)⁻¹ * Rᵀ

/-- The residualized excluded-instrument projection is orthogonal to the
maintained-instrument projection on the nonsingular maintained branch:
`P_R P_a = 0`. -/
theorem twoSLSSubsetResidualizedProjectionStar_mul_instrumentProjectionStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) [Invertible (Zaᵀ * Za)] :
    twoSLSSubsetResidualizedProjectionStar Za Zb * instrumentProjectionStar Za = 0 := by
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hZaR : Zaᵀ * R = 0 :=
    transpose_mul_twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hRZa : Rᵀ * Za = 0 := by
    have hT := congrArg Matrix.transpose hZaR
    simpa [Matrix.transpose_mul] using hT
  unfold twoSLSSubsetResidualizedProjectionStar instrumentProjectionStar
  change
    (R * (Rᵀ * R)⁻¹ * Rᵀ) * (Za * (Zaᵀ * Za)⁻¹ * Zaᵀ) = 0
  calc
    (R * (Rᵀ * R)⁻¹ * Rᵀ) * (Za * (Zaᵀ * Za)⁻¹ * Zaᵀ)
        = R * (Rᵀ * R)⁻¹ * (Rᵀ * Za) * (Zaᵀ * Za)⁻¹ * Zaᵀ := by
          simp [Matrix.mul_assoc]
    _ = 0 := by simp [hRZa]

/-- The maintained-instrument projection is orthogonal to the residualized
excluded-instrument projection on the nonsingular maintained branch:
`P_a P_R = 0`. -/
theorem instrumentProjectionStar_mul_twoSLSSubsetResidualizedProjectionStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) [Invertible (Zaᵀ * Za)] :
    instrumentProjectionStar Za * twoSLSSubsetResidualizedProjectionStar Za Zb = 0 := by
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hZaR : Zaᵀ * R = 0 :=
    transpose_mul_twoSLSSubsetResidualizedInstrumentsStar Za Zb
  unfold twoSLSSubsetResidualizedProjectionStar instrumentProjectionStar
  change
    (Za * (Zaᵀ * Za)⁻¹ * Zaᵀ) * (R * (Rᵀ * R)⁻¹ * Rᵀ) = 0
  calc
    (Za * (Zaᵀ * Za)⁻¹ * Zaᵀ) * (R * (Rᵀ * R)⁻¹ * Rᵀ)
        = Za * (Zaᵀ * Za)⁻¹ * (Zaᵀ * R) * (Rᵀ * R)⁻¹ * Rᵀ := by
          simp [Matrix.mul_assoc]
    _ = 0 := by simp [hZaR]

omit [Fintype lb] [DecidableEq lb] in
/-- The maintained-instrument projection kills the residualized excluded
instrument block: `P_a R = 0`. -/
theorem instrumentProjectionStar_mul_twoSLSSubsetResidualizedInstrumentsStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) [Invertible (Zaᵀ * Za)] :
    instrumentProjectionStar Za *
      twoSLSSubsetResidualizedInstrumentsStar Za Zb = 0 := by
  unfold twoSLSSubsetResidualizedInstrumentsStar
  rw [instrumentProjectionStar_eq_projection]
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
    instrumentProjection_idempotent]
  simp

/-- The residualized excluded-instrument projection fixes the residualized
excluded instruments when their residualized Gram matrix is nonsingular:
`P_R R = R`. -/
theorem twoSLSSubsetResidualizedProjectionStar_mul_residualizedInstrumentsStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)] :
    twoSLSSubsetResidualizedProjectionStar Za Zb *
      twoSLSSubsetResidualizedInstrumentsStar Za Zb =
        twoSLSSubsetResidualizedInstrumentsStar Za Zb := by
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  unfold twoSLSSubsetResidualizedProjectionStar
  change (R * (Rᵀ * R)⁻¹ * Rᵀ) * R = R
  calc
    (R * (Rᵀ * R)⁻¹ * Rᵀ) * R
        = R * ((Rᵀ * R)⁻¹ * (Rᵀ * R)) := by
          simp [Matrix.mul_assoc]
    _ = R * (1 : Matrix lb lb ℝ) := by
          rw [← invOf_eq_nonsing_inv (Rᵀ * R), invOf_mul_self]
    _ = R := by simp

/-- The residualized excluded-instrument projection is symmetric on the
nonsingular residualized-Gram branch. -/
theorem twoSLSSubsetResidualizedProjectionStar_transpose
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)] :
    (twoSLSSubsetResidualizedProjectionStar Za Zb)ᵀ =
      twoSLSSubsetResidualizedProjectionStar Za Zb := by
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hGram :
      (Rᵀ * R)ᵀ = Rᵀ * R := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  unfold twoSLSSubsetResidualizedProjectionStar
  change (R * (Rᵀ * R)⁻¹ * Rᵀ)ᵀ = R * (Rᵀ * R)⁻¹ * Rᵀ
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hGram]
  simp [Matrix.mul_assoc]

/-- The residualized excluded-instrument projection is idempotent on the
nonsingular residualized-Gram branch. -/
theorem twoSLSSubsetResidualizedProjectionStar_idempotent
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)] :
    twoSLSSubsetResidualizedProjectionStar Za Zb *
      twoSLSSubsetResidualizedProjectionStar Za Zb =
        twoSLSSubsetResidualizedProjectionStar Za Zb := by
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
  have hPRR : PR * R = R := by
    simpa [PR, R] using
      twoSLSSubsetResidualizedProjectionStar_mul_residualizedInstrumentsStar Za Zb
  calc
    twoSLSSubsetResidualizedProjectionStar Za Zb *
        twoSLSSubsetResidualizedProjectionStar Za Zb =
        PR * (R * ((Rᵀ * R)⁻¹ * Rᵀ)) := by
          simp [PR, R, twoSLSSubsetResidualizedProjectionStar, Matrix.mul_assoc]
    _ = (PR * R) * ((Rᵀ * R)⁻¹ * Rᵀ) := by
          rw [Matrix.mul_assoc]
    _ = PR := by
          rw [hPRR]
          simp [PR, R, twoSLSSubsetResidualizedProjectionStar, Matrix.mul_assoc]

/-- The residualized excluded-instrument projection kills the maintained
instrument block: `P_R Z_a = 0`. -/
theorem twoSLSSubsetResidualizedProjectionStar_mul_Za
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) [Invertible (Zaᵀ * Za)] :
    twoSLSSubsetResidualizedProjectionStar Za Zb * Za = 0 := by
  calc
    twoSLSSubsetResidualizedProjectionStar Za Zb * Za =
        twoSLSSubsetResidualizedProjectionStar Za Zb *
          (instrumentProjectionStar Za * Za) := by
          rw [instrumentProjectionStar_mul_Z_of_nonsingular]
    _ = (twoSLSSubsetResidualizedProjectionStar Za Zb *
          instrumentProjectionStar Za) * Za := by
          rw [Matrix.mul_assoc]
    _ = 0 := by
          rw [twoSLSSubsetResidualizedProjectionStar_mul_instrumentProjectionStar,
            Matrix.zero_mul]

/-- The residualized excluded-instrument projection maps the raw excluded block
to its residualized block: `P_R Z_b = R`. -/
theorem twoSLSSubsetResidualizedProjectionStar_mul_Zb
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)] :
    twoSLSSubsetResidualizedProjectionStar Za Zb * Zb =
      twoSLSSubsetResidualizedInstrumentsStar Za Zb := by
  have hdecomp :
      instrumentProjectionStar Za * Zb +
          twoSLSSubsetResidualizedInstrumentsStar Za Zb = Zb := by
    unfold twoSLSSubsetResidualizedInstrumentsStar
    rw [Matrix.sub_mul, Matrix.one_mul]
    ext i j
    simp
  calc
    twoSLSSubsetResidualizedProjectionStar Za Zb * Zb =
        twoSLSSubsetResidualizedProjectionStar Za Zb *
          (instrumentProjectionStar Za * Zb +
            twoSLSSubsetResidualizedInstrumentsStar Za Zb) := by
          rw [hdecomp]
    _ = twoSLSSubsetResidualizedProjectionStar Za Zb *
          (instrumentProjectionStar Za * Zb) +
        twoSLSSubsetResidualizedProjectionStar Za Zb *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb := by
          rw [Matrix.mul_add]
    _ = (twoSLSSubsetResidualizedProjectionStar Za Zb *
          instrumentProjectionStar Za) * Zb +
        twoSLSSubsetResidualizedInstrumentsStar Za Zb := by
          rw [Matrix.mul_assoc,
            twoSLSSubsetResidualizedProjectionStar_mul_residualizedInstrumentsStar]
    _ = twoSLSSubsetResidualizedInstrumentsStar Za Zb := by
          rw [twoSLSSubsetResidualizedProjectionStar_mul_instrumentProjectionStar]
          simp

/-- Block form of the residualized projection range identity:
`P_R [Z_a,Z_b] = [0,R]`. -/
theorem twoSLSSubsetResidualizedProjectionStar_mul_fromCols
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)] :
    twoSLSSubsetResidualizedProjectionStar Za Zb *
        Matrix.fromCols Za Zb =
      Matrix.fromCols (0 : Matrix n la ℝ)
        (twoSLSSubsetResidualizedInstrumentsStar Za Zb) := by
  rw [Matrix.mul_fromCols, twoSLSSubsetResidualizedProjectionStar_mul_Za,
    twoSLSSubsetResidualizedProjectionStar_mul_Zb]

omit [Fintype k] [DecidableEq k] in
/-- Hansen's finite-sample projection decomposition for a partitioned
instrument matrix:
`P_[Z_a,Z_b] = P_a + P_R`, where `R = M_a Z_b`.

This is the deterministic range decomposition used in Hansen Theorem 12.17
before the Schur-complement and Woodbury steps. -/
theorem instrumentProjectionStar_fromCols_eq_sum_residualizedProjectionStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)] :
    instrumentProjectionStar (Matrix.fromCols Za Zb) =
      instrumentProjectionStar Za +
        twoSLSSubsetResidualizedProjectionStar Za Zb := by
  let Z := Matrix.fromCols Za Zb
  let PZ := instrumentProjectionStar Z
  let Pa := instrumentProjectionStar Za
  let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hPZ_Z : PZ * Z = Z := by
    simpa [PZ, Z] using instrumentProjectionStar_mul_Z_of_nonsingular
      (Matrix.fromCols Za Zb)
  have hPZ_Za : PZ * Za = Za := by
    ext i a
    have h := congrArg (fun M : Matrix n (la ⊕ lb) ℝ => M i (Sum.inl a)) hPZ_Z
    simpa [Z, Matrix.mul_fromCols] using h
  have hPZ_Zb : PZ * Zb = Zb := by
    ext i b
    have h := congrArg (fun M : Matrix n (la ⊕ lb) ℝ => M i (Sum.inr b)) hPZ_Z
    simpa [Z, Matrix.mul_fromCols] using h
  have hPa_Za : Pa * Za = Za := by
    simpa [Pa] using instrumentProjectionStar_mul_Z_of_nonsingular Za
  have hPa_expand : Pa = Za * (Zaᵀ * Za)⁻¹ * Zaᵀ := by
    dsimp [Pa, instrumentProjectionStar]
  have hPZ_Pa : PZ * Pa = Pa := by
    calc
      PZ * Pa = PZ * (Za * (Zaᵀ * Za)⁻¹ * Zaᵀ) := by rw [hPa_expand]
      _ = (PZ * Za) * (Zaᵀ * Za)⁻¹ * Zaᵀ := by
        simp [Matrix.mul_assoc]
      _ = Za * (Zaᵀ * Za)⁻¹ * Zaᵀ := by rw [hPZ_Za]
      _ = Pa := hPa_expand.symm
  have hPZ_R : PZ * R = R := by
    dsimp [R, twoSLSSubsetResidualizedInstrumentsStar]
    change PZ * (((1 : Matrix n n ℝ) - Pa) * Zb) =
      ((1 : Matrix n n ℝ) - Pa) * Zb
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPZ_Pa,
      Matrix.sub_mul, hPZ_Zb, Matrix.sub_mul, Matrix.one_mul]
  have hPZ_PR : PZ * PR = PR := by
    calc
      PZ * PR = (PZ * R) * (Rᵀ * R)⁻¹ * Rᵀ := by
        simp [PR, R, twoSLSSubsetResidualizedProjectionStar, Matrix.mul_assoc]
      _ = PR := by
        rw [hPZ_R]
        simp [PR, R, twoSLSSubsetResidualizedProjectionStar, Matrix.mul_assoc]
  have hPZ_Psum : PZ * (Pa + PR) = Pa + PR := by
    rw [Matrix.mul_add, hPZ_Pa, hPZ_PR]
  have hPaT : Paᵀ = Pa := by
    simpa [Pa] using instrumentProjectionStar_transpose_of_nonsingular Za
  have hPRT : PRᵀ = PR := by
    simpa [PR] using twoSLSSubsetResidualizedProjectionStar_transpose Za Zb
  have hPZT : PZᵀ = PZ := by
    simpa [PZ, Z] using instrumentProjectionStar_transpose_of_nonsingular
      (Matrix.fromCols Za Zb)
  have hPsum_PZ_eq_Psum : (Pa + PR) * PZ = Pa + PR := by
    have hT := congrArg Matrix.transpose hPZ_Psum
    simpa [Matrix.transpose_mul, Matrix.transpose_add, hPZT, hPaT, hPRT] using hT
  have hPR_Za : PR * Za = 0 := by
    simpa [PR] using twoSLSSubsetResidualizedProjectionStar_mul_Za Za Zb
  have hPR_Zb : PR * Zb = R := by
    simpa [PR, R] using twoSLSSubsetResidualizedProjectionStar_mul_Zb Za Zb
  have hPsum_Z : (Pa + PR) * Z = Z := by
    ext i j
    cases j with
    | inl a =>
        have h :=
          congrArg (fun M : Matrix n la ℝ => M i a)
            (by
              rw [Matrix.add_mul, hPa_Za, hPR_Za]
              simp : (Pa + PR) * Za = Za)
        simpa [Z, Matrix.mul_fromCols] using h
    | inr b =>
        have hdecomp :
            Pa * Zb + R = Zb := by
          dsimp [R, twoSLSSubsetResidualizedInstrumentsStar]
          change Pa * Zb + (((1 : Matrix n n ℝ) - Pa) * Zb) = Zb
          rw [Matrix.sub_mul, Matrix.one_mul]
          ext i b
          simp
        have h :=
          congrArg (fun M : Matrix n lb ℝ => M i b)
            (by
              rw [Matrix.add_mul, hPR_Zb, hdecomp]
              : (Pa + PR) * Zb = Zb)
        simpa [Z, Matrix.mul_fromCols] using h
  have hPsum_PZ_eq_PZ : (Pa + PR) * PZ = PZ := by
    have hPZ_expand : PZ = Z * (Zᵀ * Z)⁻¹ * Zᵀ := by
      dsimp [PZ, instrumentProjectionStar]
    calc
      (Pa + PR) * PZ =
          (Pa + PR) * (Z * (Zᵀ * Z)⁻¹ * Zᵀ) := by rw [hPZ_expand]
      _ = ((Pa + PR) * Z) * (Zᵀ * Z)⁻¹ * Zᵀ := by
            simp [Matrix.mul_assoc]
      _ = Z * (Zᵀ * Z)⁻¹ * Zᵀ := by rw [hPsum_Z]
      _ = PZ := hPZ_expand.symm
  calc
    PZ = (Pa + PR) * PZ := hPsum_PZ_eq_PZ.symm
    _ = Pa + PR := hPsum_PZ_eq_Psum

omit [Fintype k] [DecidableEq k] in
/-- The Schur-complement premise for Newey's Woodbury kernel follows from
Hansen's projection decomposition `P_[Z_a,Z_b] = P_a + P_R`.

This packages the deterministic step needed by
`twoSLSSubsetNeweyKernelStar_eq_residualizedProjectionStar_add_fittedCorrection_of_schur`.
-/
theorem twoSLSSubsetSchurComplement_eq_restrictedMomentMatrix_of_projection_decomposition
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hprojection : instrumentProjectionStar (Matrix.fromCols Za Zb) =
      instrumentProjectionStar Za +
        twoSLSSubsetResidualizedProjectionStar Za Zb) :
    twoSLSMomentMatrixStar Za X =
      (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X -
        (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb *
          ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar Za Zb)⁻¹ *
          (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X := by
  let Z := Matrix.fromCols Za Zb
  let Pa := instrumentProjectionStar Za
  let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let Xhat := fittedRegressorsStar Z X
  have hprojectionZ : instrumentProjectionStar Z = Pa + PR := by
    simpa [Z, Pa, PR] using hprojection
  have hXhat : Xhat = (Pa + PR) * X := by
    dsimp [Xhat, fittedRegressorsStar, Z, Pa, PR]
    rw [hprojectionZ]
  have hPZT : (instrumentProjectionStar Z)ᵀ = instrumentProjectionStar Z := by
    simpa [Z] using instrumentProjectionStar_transpose_of_nonsingular
      (Matrix.fromCols Za Zb)
  have hPZIdem :
      instrumentProjectionStar Z * instrumentProjectionStar Z =
        instrumentProjectionStar Z := by
    simpa [Z] using instrumentProjectionStar_idempotent_of_nonsingular
      (Matrix.fromCols Za Zb)
  have hPaT : Paᵀ = Pa := by
    simpa [Pa] using instrumentProjectionStar_transpose_of_nonsingular Za
  have hPRT : PRᵀ = PR := by
    simpa [PR] using twoSLSSubsetResidualizedProjectionStar_transpose Za Zb
  have hPaR : Pa * R = 0 := by
    simpa [Pa, R] using
      instrumentProjectionStar_mul_twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hPRR : PR * R = R := by
    simpa [PR, R] using
      twoSLSSubsetResidualizedProjectionStar_mul_residualizedInstrumentsStar Za Zb
  have hRTPa : Rᵀ * Pa = 0 := by
    have h := congrArg Matrix.transpose hPaR
    simpa [Matrix.transpose_mul, hPaT] using h
  have hRTPR : Rᵀ * PR = Rᵀ := by
    have h := congrArg Matrix.transpose hPRR
    simpa [Matrix.transpose_mul, hPRT] using h
  have hsumR : (Pa + PR) * R = R := by
    rw [Matrix.add_mul, hPaR, hPRR]
    simp
  have hRsum : Rᵀ * (Pa + PR) = Rᵀ := by
    rw [Matrix.mul_add, hRTPa, hRTPR]
    simp
  have hgram :
      Xhatᵀ * Xhat = Xᵀ * Pa * X + Xᵀ * PR * X := by
    calc
      Xhatᵀ * Xhat =
          Xᵀ * ((instrumentProjectionStar Z)ᵀ * instrumentProjectionStar Z) * X := by
        simp [Xhat, fittedRegressorsStar, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Xᵀ * instrumentProjectionStar Z * X := by
        rw [hPZT, hPZIdem]
      _ = Xᵀ * (Pa + PR) * X := by
        rw [hprojectionZ]
      _ = Xᵀ * Pa * X + Xᵀ * PR * X := by
        rw [Matrix.mul_add, Matrix.add_mul]
  have hcorrection :
      Xhatᵀ * R * (Rᵀ * R)⁻¹ * Rᵀ * Xhat = Xᵀ * PR * X := by
    calc
      Xhatᵀ * R * (Rᵀ * R)⁻¹ * Rᵀ * Xhat =
          (((Pa + PR) * X)ᵀ * R) * (Rᵀ * R)⁻¹ * Rᵀ *
            ((Pa + PR) * X) := by
            rw [hXhat]
      _ = Xᵀ * ((Pa + PR)ᵀ * R) * (Rᵀ * R)⁻¹ *
          (Rᵀ * ((Pa + PR) * X)) := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Xᵀ * ((Pa + PR) * R) * (Rᵀ * R)⁻¹ *
          ((Rᵀ * (Pa + PR)) * X) := by
            rw [Matrix.transpose_add, hPaT, hPRT]
            simp [Matrix.mul_assoc]
      _ = Xᵀ * R * (Rᵀ * R)⁻¹ * (Rᵀ * X) := by
            rw [hsumR, hRsum]
      _ = Xᵀ * PR * X := by
            simp [PR, twoSLSSubsetResidualizedProjectionStar, R, Matrix.mul_assoc]
  calc
    twoSLSMomentMatrixStar Za X = Xᵀ * Pa * X := by
      simp [twoSLSMomentMatrixStar, Pa, Matrix.mul_assoc]
    _ = Xhatᵀ * Xhat -
        Xhatᵀ * R * (Rᵀ * R)⁻¹ * Rᵀ * Xhat := by
          rw [hgram, hcorrection]
          abel

omit [Fintype k] [DecidableEq k] in
/-- Schur-complement identity for Hansen Theorem 12.17 with the projection
decomposition proved internally from the partitioned-instrument design. -/
theorem twoSLSSubsetSchurComplement_eq_restrictedMomentMatrix
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)] :
    twoSLSMomentMatrixStar Za X =
      (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X -
        (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb *
          ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar Za Zb)⁻¹ *
          (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X :=
  twoSLSSubsetSchurComplement_eq_restrictedMomentMatrix_of_projection_decomposition
    Za Zb X
    (instrumentProjectionStar_fromCols_eq_sum_residualizedProjectionStar Za Zb)

/-- The maintained-moment Schur complement is nonsingular whenever Hansen's
maintained-model moment matrix is nonsingular.

This is the finite-sample companion to
`twoSLSSubsetSchurComplement_eq_restrictedMomentMatrix`: once the
maintained-instrument moment matrix is nonsingular, the algebraically identical
Schur complement inherits that nonsingularity. -/
theorem twoSLSSubsetSchurComplement_invertible_of_restrictedMomentMatrix
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hMaintained :
      Nonempty (Invertible (twoSLSMomentMatrixStar Za X))) :
    Nonempty (Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X -
        (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb *
          ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar Za Zb)⁻¹ *
          (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X)) := by
  simpa [← twoSLSSubsetSchurComplement_eq_restrictedMomentMatrix Za Zb X]
    using hMaintained

/-- The dual Schur-complement branch used in Newey's Woodbury identity follows
from the residualized-instrument Gram, full fitted-regressor Gram, and
maintained-model moment branches.

This is deliberately stronger than the maintained moment branch alone: the
dual complement `R'R - R'X̂(X̂'X̂)^{-1}X̂'R` is derived through the common block
matrix and therefore also needs nonsingularity of `R'R` and `X̂'X̂`. -/
theorem twoSLSSubsetDualSchurComplement_invertible_of_normalEquations
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    [Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
        fittedRegressorsStar (Matrix.fromCols Za Zb) X)]
    [Invertible (twoSLSMomentMatrixStar Za X)] :
    Nonempty (Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb -
        (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X *
          ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
            fittedRegressorsStar (Matrix.fromCols Za Zb) X)⁻¹ *
          (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb)) := by
  let Z := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let Xhat := fittedRegressorsStar Z X
  let G : Matrix lb lb ℝ := Rᵀ * R
  let S : Matrix k k ℝ := Xhatᵀ * Xhat
  let A : Matrix k k ℝ := twoSLSMomentMatrixStar Za X
  let U : Matrix lb k ℝ := Rᵀ * Xhat
  let V : Matrix k lb ℝ := Xhatᵀ * R
  have hA : A = S - V * G⁻¹ * U := by
    simpa [A, S, V, G, U, Xhat, R, Z, Matrix.mul_assoc] using
      twoSLSSubsetSchurComplement_eq_restrictedMomentMatrix Za Zb X
  simpa [G, U, S, V, R, Xhat, Z, Matrix.mul_assoc] using
    dual_schur_sub_nonsingInv_invertible_of_primal G U S A V hA

omit [DecidableEq n] [Fintype la] [DecidableEq la] [Fintype lb] [DecidableEq lb] in
/-- The full 2SLS moment determinant branch follows from nonsingularity of the
fitted-regressor Gram.

For Hansen Theorem 12.17 this removes a redundant finite-sample side condition:
on the nonsingular instrument branch, `(P_Z X)'(P_Z X) = X'P_Z X`, so an
invertible fitted-regressor Gram already supplies the determinant certificate
needed by the Star 2SLS normal-equation identities. -/
theorem twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ)
    [Invertible (Zᵀ * Z)]
    (hFitted : Nonempty (Invertible
      ((fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X))) :
    IsUnit (twoSLSMomentMatrixStar Z X).det := by
  classical
  rcases hFitted with ⟨instFitted⟩
  letI : Invertible
      ((fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X) := instFitted
  have hPX :
      instrumentProjectionStar Z * (instrumentProjectionStar Z * X) =
        instrumentProjectionStar Z * X := by
    rw [← Matrix.mul_assoc, instrumentProjectionStar_idempotent_of_nonsingular]
  have hgram :
      (fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X =
        twoSLSMomentMatrixStar Z X := by
    unfold fittedRegressorsStar twoSLSMomentMatrixStar
    rw [Matrix.transpose_mul, instrumentProjectionStar_transpose_of_nonsingular]
    simpa [Matrix.mul_assoc] using
      congrArg (fun M : Matrix n k ℝ => Xᵀ * M) hPX
  have hfit :
      IsUnit (((fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X).det) :=
    Matrix.isUnit_det_of_invertible _
  simpa [hgram] using hfit

omit [DecidableEq n] in
/-- Nonsingularity of the fitted-regressor Gram gives nonsingularity of the
2SLS moment matrix.

This is the `Nonempty (Invertible ...)` companion to
`twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible`.
It lets Theorem 12.17 finite-sample normal-equation routes use the same
fitted-Gram regularity language for the maintained and full specifications. -/
theorem twoSLSMomentMatrixStar_invertible_of_fittedRegressorsStar_gram_invertible
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ)
    [Invertible (Zᵀ * Z)]
    (hFitted : Nonempty (Invertible
      ((fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X))) :
    Nonempty (Invertible (twoSLSMomentMatrixStar Z X)) :=
  ⟨Matrix.invertibleOfIsUnitDet (A := twoSLSMomentMatrixStar Z X)
    (twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible
      Z X hFitted)⟩

/-- Newey's subset-overidentification statistic `N` for testing the validity of
the `Z_b` block under maintained validity of `Z_a`. -/
noncomputable def twoSLSSubsetNeweyStatOrZero
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  let Z := Matrix.fromCols Za Zb
  let ehat := twoSLSResidualStar Z X Y
  let Xhat := fittedRegressorsStar Z X
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let middle := Rᵀ * R - Rᵀ * Xhat * (Xhatᵀ * Xhat)⁻¹ * Xhatᵀ * R
  ehat ⬝ᵥ ((R * middle⁻¹ * Rᵀ) *ᵥ ehat) / twoSLSSigmaSqHatStar Z X Y

/-- Middle covariance matrix in Newey's subset-overidentification statistic. -/
noncomputable def twoSLSSubsetNeweyMiddleStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ) :
    Matrix lb lb ℝ :=
  let Z := Matrix.fromCols Za Zb
  let Xhat := fittedRegressorsStar Z X
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  Rᵀ * R - Rᵀ * Xhat * (Xhatᵀ * Xhat)⁻¹ * Xhatᵀ * R

/-- Residualized excluded-instrument score in Newey's subset-overidentification
statistic. -/
noncomputable def twoSLSSubsetResidualizedScoreStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : lb → ℝ :=
  let Z := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  Rᵀ *ᵥ twoSLSResidualStar Z X Y

/-- Sample linear map from the full-instrument residual score
`[Z_a,Z_b]' ê` to Newey's residualized excluded-instrument score `R' ê`.

Writing this map explicitly lets the subset-score CLT reuse the full Sargan
residual-score CLT plus a rectangular Slutsky step. -/
noncomputable def twoSLSSubsetResidualizedScoreMapStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) : Matrix lb (la ⊕ lb) ℝ :=
  let Z := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  Rᵀ * Z * (Zᵀ * Z)⁻¹

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] in
/-- Population/sample Gram form of the residualized excluded-instrument score
map.  For a full instrument Gram `Q` partitioned as `[Z_a,Z_b]`, this is
`(Q_b· - Q_ba Q_aa^{-1} Q_a·) Q^{-1}`.  It is the continuous-map target used to
derive the sample map in Hansen Theorem 12.17 from one full-instrument
sample-Gram WLLN. -/
noncomputable def twoSLSSubsetResidualizedScoreMapFromGram
    (Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) : Matrix lb (la ⊕ lb) ℝ :=
  (Q.submatrix Sum.inr id -
      Q.submatrix Sum.inr Sum.inl * (Q.submatrix Sum.inl Sum.inl)⁻¹ *
        Q.submatrix Sum.inl id) * Q⁻¹

omit [DecidableEq n] [Fintype la] [DecidableEq la] [Fintype lb] [DecidableEq lb] in
private theorem sampleGram_fromCols_right_full
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) :
    (sampleGram (Matrix.fromCols Za Zb)).submatrix Sum.inr id =
      (Fintype.card n : ℝ)⁻¹ • (Zbᵀ * Matrix.fromCols Za Zb) := by
  ext b j
  cases j <;> simp [sampleGram, Matrix.mul_apply]

omit [DecidableEq n] [Fintype la] [DecidableEq la] [Fintype lb] [DecidableEq lb] in
private theorem sampleGram_fromCols_left_full
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) :
    (sampleGram (Matrix.fromCols Za Zb)).submatrix Sum.inl id =
      (Fintype.card n : ℝ)⁻¹ • (Zaᵀ * Matrix.fromCols Za Zb) := by
  ext a j
  cases j <;> simp [sampleGram, Matrix.mul_apply]

omit [DecidableEq n] [Fintype la] [DecidableEq la] [Fintype lb] [DecidableEq lb] in
private theorem sampleGram_fromCols_right_left_raw
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) :
    (sampleGram (Matrix.fromCols Za Zb)).submatrix Sum.inr Sum.inl =
      (Fintype.card n : ℝ)⁻¹ • (Zbᵀ * Za) := by
  ext b a
  simp [sampleGram, Matrix.mul_apply]

omit [DecidableEq n] [Fintype la] [DecidableEq la] [Fintype lb] [DecidableEq lb] in
private theorem sampleGram_fromCols_left_left_raw
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) :
    (sampleGram (Matrix.fromCols Za Zb)).submatrix Sum.inl Sum.inl =
      (Fintype.card n : ℝ)⁻¹ • (Zaᵀ * Za) := by
  ext a b
  simp [sampleGram, Matrix.mul_apply]

omit [Fintype lb] [DecidableEq lb] in
private theorem residualizedInstrumentsStar_transpose_mul_fromCols
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) :
    (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        Matrix.fromCols Za Zb =
      Zbᵀ * Matrix.fromCols Za Zb -
        Zbᵀ * Za * (Zaᵀ * Za)⁻¹ * (Zaᵀ * Matrix.fromCols Za Zb) := by
  let Pa := instrumentProjectionStar Za
  have hPaT : Paᵀ = Pa := by
    dsimp [Pa, instrumentProjectionStar]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, gram_transpose]
    simp [Matrix.mul_assoc]
  unfold twoSLSSubsetResidualizedInstrumentsStar
  change (((1 : Matrix n n ℝ) - Pa) * Zb)ᵀ * Matrix.fromCols Za Zb =
    Zbᵀ * Matrix.fromCols Za Zb -
      Zbᵀ * Za * (Zaᵀ * Za)⁻¹ * (Zaᵀ * Matrix.fromCols Za Zb)
  calc
    (((1 : Matrix n n ℝ) - Pa) * Zb)ᵀ * Matrix.fromCols Za Zb =
        Zbᵀ * ((1 : Matrix n n ℝ) - Pa)ᵀ * Matrix.fromCols Za Zb := by
          rw [Matrix.transpose_mul]
    _ = Zbᵀ * ((1 : Matrix n n ℝ) - Pa) * Matrix.fromCols Za Zb := by
          rw [Matrix.transpose_sub, Matrix.transpose_one, hPaT]
    _ = Zbᵀ * Matrix.fromCols Za Zb -
        Zbᵀ * Za * (Zaᵀ * Za)⁻¹ * (Zaᵀ * Matrix.fromCols Za Zb) := by
          simp [Pa, instrumentProjectionStar, Matrix.sub_mul, Matrix.mul_sub,
            Matrix.mul_assoc]

omit [Fintype k] [DecidableEq k] in
/-- Finite-sample block-normalization bridge for Hansen Theorem 12.17:
the concrete Star residualized-score map is the Gram-form map evaluated at the
full partitioned sample Gram. -/
theorem twoSLSSubsetResidualizedScoreMapStar_eq_fromGram_sampleGram
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) [Nonempty n] :
    twoSLSSubsetResidualizedScoreMapStar Za Zb =
      twoSLSSubsetResidualizedScoreMapFromGram
        (sampleGram (Matrix.fromCols Za Zb)) := by
  classical
  let Z := Matrix.fromCols Za Zb
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc : c ≠ 0 := inv_ne_zero hcard
  have hcinv : c⁻¹ = (Fintype.card n : ℝ) := by
    simp [c]
  have hQinv :
      (sampleGram (Matrix.fromCols Za Zb))⁻¹ =
        c⁻¹ • ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)⁻¹ := by
    simp [sampleGram, c, nonsingInv_smul]
  have hRZ :
      (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ * Z =
        Zbᵀ * Z - Zbᵀ * Za * (Zaᵀ * Za)⁻¹ * (Zaᵀ * Z) := by
    simpa [Z] using residualizedInstrumentsStar_transpose_mul_fromCols Za Zb
  unfold twoSLSSubsetResidualizedScoreMapStar
    twoSLSSubsetResidualizedScoreMapFromGram
  change
    (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ * Z * (Zᵀ * Z)⁻¹ =
      ((sampleGram Z).submatrix Sum.inr id -
          (sampleGram Z).submatrix Sum.inr Sum.inl *
            ((sampleGram Z).submatrix Sum.inl Sum.inl)⁻¹ *
              (sampleGram Z).submatrix Sum.inl id) *
        (sampleGram Z)⁻¹
  have hRightFull :
      (sampleGram Z).submatrix Sum.inr id = c • (Zbᵀ * Z) := by
    simpa [Z, c] using sampleGram_fromCols_right_full Za Zb
  have hLeftFull :
      (sampleGram Z).submatrix Sum.inl id = c • (Zaᵀ * Z) := by
    simpa [Z, c] using sampleGram_fromCols_left_full Za Zb
  have hRightLeft :
      (sampleGram Z).submatrix Sum.inr Sum.inl = c • (Zbᵀ * Za) := by
    simpa [Z, c] using sampleGram_fromCols_right_left_raw Za Zb
  have hLeftLeft :
      (sampleGram Z).submatrix Sum.inl Sum.inl = c • (Zaᵀ * Za) := by
    simpa [Z, c] using sampleGram_fromCols_left_left_raw Za Zb
  have hQinvZ : (sampleGram Z)⁻¹ = c⁻¹ • (Zᵀ * Z)⁻¹ := by
    simpa [Z] using hQinv
  rw [hRightFull, hRightLeft, hLeftLeft, hLeftFull, hQinvZ]
  rw [nonsingInv_smul, hcinv, hRZ]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  simp only [c, mul_inv_cancel₀ hcard, mul_one]
  let A : Matrix lb (la ⊕ lb) ℝ := Zbᵀ * Z
  let B : Matrix lb (la ⊕ lb) ℝ :=
    Zbᵀ * (Za * ((Zaᵀ * Za)⁻¹ * (Zaᵀ * Z)))
  let G : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := (Zᵀ * Z)⁻¹
  change (A - B) * G =
    (Fintype.card n : ℝ) •
      (((Fintype.card n : ℝ)⁻¹ • A - (Fintype.card n : ℝ)⁻¹ • B) * G)
  have hscale :
      (Fintype.card n : ℝ) • ((Fintype.card n : ℝ)⁻¹ • (A - B)) =
        A - B := by
    rw [smul_smul, mul_inv_cancel₀ hcard, one_smul]
  calc
    (A - B) * G =
        ((Fintype.card n : ℝ) • ((Fintype.card n : ℝ)⁻¹ • (A - B))) * G := by
          rw [hscale]
    _ = (Fintype.card n : ℝ) •
        (((Fintype.card n : ℝ)⁻¹ • (A - B)) * G) := by
          rw [Matrix.smul_mul]
    _ = (Fintype.card n : ℝ) •
        (((Fintype.card n : ℝ)⁻¹ • A - (Fintype.card n : ℝ)⁻¹ • B) * G) := by
          rw [smul_sub]

set_option maxHeartbeats 600000 in
-- Matrix continuity through nested submatrices and total inverses is expensive here.
omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] in
/-- The Gram-form residualized score map is continuous at nonsingular full and
maintained population instrument Grams. -/
theorem twoSLSSubsetResidualizedScoreMapFromGram_continuousAt
    (Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ)
    (hQaa : IsUnit (Q.submatrix Sum.inl Sum.inl).det)
    (hQ : IsUnit Q.det) :
    ContinuousAt twoSLSSubsetResidualizedScoreMapFromGram Q := by
  let Qaa : Matrix la la ℝ := Q.submatrix Sum.inl Sum.inl
  have hQaaMap :
      ContinuousAt (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ =>
        Q'.submatrix Sum.inl Sum.inl) Q :=
    (continuous_id.matrix_submatrix Sum.inl Sum.inl).continuousAt
  have hQaaInv : ContinuousAt
      (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ =>
        (Q'.submatrix Sum.inl Sum.inl)⁻¹) Q := by
    have hInv : ContinuousAt Inv.inv Qaa := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hQaa.ne_zero
    simpa [Qaa] using hInv.comp hQaaMap
  have hQInv : ContinuousAt
      (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ => Q'⁻¹) Q := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hQ.ne_zero
  have hQb : ContinuousAt
      (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ => Q'.submatrix Sum.inr id) Q :=
    (continuous_id.matrix_submatrix Sum.inr id).continuousAt
  have hQba : ContinuousAt
      (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ =>
        Q'.submatrix Sum.inr Sum.inl) Q :=
    (continuous_id.matrix_submatrix Sum.inr Sum.inl).continuousAt
  have hQa : ContinuousAt
      (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ => Q'.submatrix Sum.inl id) Q :=
    (continuous_id.matrix_submatrix Sum.inl id).continuousAt
  have hQbaInv : ContinuousAt
      (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ =>
        Q'.submatrix Sum.inr Sum.inl * (Q'.submatrix Sum.inl Sum.inl)⁻¹) Q :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hQba.prodMk hQaaInv)
  have hCorrection : ContinuousAt
      (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ =>
        Q'.submatrix Sum.inr Sum.inl * (Q'.submatrix Sum.inl Sum.inl)⁻¹ *
          Q'.submatrix Sum.inl id) Q :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hQbaInv.prodMk hQa)
  have hMiddle : ContinuousAt
      (fun Q' : Matrix (la ⊕ lb) (la ⊕ lb) ℝ =>
        Q'.submatrix Sum.inr id -
          Q'.submatrix Sum.inr Sum.inl * (Q'.submatrix Sum.inl Sum.inl)⁻¹ *
            Q'.submatrix Sum.inl id) Q :=
    hQb.sub hCorrection
  unfold twoSLSSubsetResidualizedScoreMapFromGram
  exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
    (hMiddle.prodMk hQInv)

set_option maxHeartbeats 600000 in
-- The proof mirrors the continuity lemma at the a.e.-measurability level.
omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] in
/-- Measurability of the Gram-form residualized score map from measurability of
the underlying partitioned Gram. -/
theorem twoSLSSubsetResidualizedScoreMapFromGram_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Q : Ω → Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    (hQ : AEStronglyMeasurable Q μ) :
    AEStronglyMeasurable
      (fun ω => twoSLSSubsetResidualizedScoreMapFromGram (Q ω)) μ := by
  have hQaa : AEStronglyMeasurable
      (fun ω => (Q ω).submatrix Sum.inl Sum.inl) μ :=
    (continuous_id.matrix_submatrix Sum.inl Sum.inl).comp_aestronglyMeasurable hQ
  have hQaaInv : AEStronglyMeasurable
      (fun ω => ((Q ω).submatrix Sum.inl Sum.inl)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hQaa
  have hQInv : AEStronglyMeasurable (fun ω => (Q ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hQ
  have hQb : AEStronglyMeasurable
      (fun ω => (Q ω).submatrix Sum.inr id) μ :=
    (continuous_id.matrix_submatrix Sum.inr id).comp_aestronglyMeasurable hQ
  have hQba : AEStronglyMeasurable
      (fun ω => (Q ω).submatrix Sum.inr Sum.inl) μ :=
    (continuous_id.matrix_submatrix Sum.inr Sum.inl).comp_aestronglyMeasurable hQ
  have hQa : AEStronglyMeasurable
      (fun ω => (Q ω).submatrix Sum.inl id) μ :=
    (continuous_id.matrix_submatrix Sum.inl id).comp_aestronglyMeasurable hQ
  have hQbaInv : AEStronglyMeasurable
      (fun ω => (Q ω).submatrix Sum.inr Sum.inl *
        ((Q ω).submatrix Sum.inl Sum.inl)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQba.prodMk hQaaInv)
  have hCorrection : AEStronglyMeasurable
      (fun ω => (Q ω).submatrix Sum.inr Sum.inl *
        ((Q ω).submatrix Sum.inl Sum.inl)⁻¹ * (Q ω).submatrix Sum.inl id) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQbaInv.prodMk hQa)
  have hMiddle : AEStronglyMeasurable
      (fun ω => (Q ω).submatrix Sum.inr id -
        (Q ω).submatrix Sum.inr Sum.inl *
          ((Q ω).submatrix Sum.inl Sum.inl)⁻¹ * (Q ω).submatrix Sum.inl id) μ :=
    hQb.sub hCorrection
  unfold twoSLSSubsetResidualizedScoreMapFromGram
  exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hMiddle.prodMk hQInv)

set_option maxHeartbeats 600000 in
-- Local inverse continuity makes the CMT proof heavier than a global map would be.
omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] in
/-- Convergence of the full partitioned instrument sample Gram gives convergence
of Hansen Theorem 12.17's residualized-score map written in Gram form.

This is the main CMT bridge for the subset-specific `hA` input: callers can
prove one WLLN for `[Z_a,Z_b]` and obtain the limit
`(Q_b· - Q_ba Q_aa^{-1} Q_a·) Q^{-1}`. -/
theorem twoSLSSubsetResidualizedScoreMapFromGram_tendstoInMeasure_of_full_instrument_sampleGram
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    (hGram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ)
    (hGram : TendstoInMeasure μ
      (fun m ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => Q))
    (hQaa : IsUnit (Q.submatrix Sum.inl Sum.inl).det)
    (hQ : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapFromGram
          (sampleGram
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
      atTop (fun _ => twoSLSSubsetResidualizedScoreMapFromGram Q) := by
  have hMap_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapFromGram
          (sampleGram
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))) μ := by
    intro m
    exact twoSLSSubsetResidualizedScoreMapFromGram_aestronglyMeasurable
      (μ := μ) (Q := fun ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      (hGram_meas m)
  exact tendstoInMeasure_continuousAt_const_comp hGram_meas hMap_meas hGram
    (twoSLSSubsetResidualizedScoreMapFromGram_continuousAt Q hQaa hQ)

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] in
/-- Convergence of the concrete residualized-score map from the full
instrument-Gram WLLN, once the finite-sample star map is identified with the
Gram-form expression eventually. -/
theorem
    twoSLSSubsetResidualizedScoreMapStar_tendstoInMeasure_of_fullSampleGram_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    (hGram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ)
    (hGram : TendstoInMeasure μ
      (fun m ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => Q))
    (hQaa : IsUnit (Q.submatrix Sum.inl Sum.inl).det)
    (hQ : IsUnit Q.det)
    (hEq : ∀ᶠ m in atTop,
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) =ᵐ[μ]
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapFromGram
          (sampleGram
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => twoSLSSubsetResidualizedScoreMapFromGram Q) := by
  have hFromGram :=
    twoSLSSubsetResidualizedScoreMapFromGram_tendstoInMeasure_of_full_instrument_sampleGram
      (μ := μ) (Za := Za) (Zb := Zb) (Q := Q)
      hGram_meas hGram hQaa hQ
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hFromGram
  filter_upwards [hEq] with m hm
  exact hm.symm

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] in
/-- Convergence of the concrete residualized-score map from the full
instrument-Gram WLLN.  The finite-sample star-vs-Gram identification is derived
internally for all sufficiently large sample sizes. -/
theorem twoSLSSubsetResidualizedScoreMapStar_tendstoInMeasure_of_fullSampleGram
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    (hGram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ)
    (hGram : TendstoInMeasure μ
      (fun m ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => Q))
    (hQaa : IsUnit (Q.submatrix Sum.inl Sum.inl).det)
    (hQ : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => twoSLSSubsetResidualizedScoreMapFromGram Q) := by
  refine
    twoSLSSubsetResidualizedScoreMapStar_tendstoInMeasure_of_fullSampleGram_eq
      (μ := μ) (Za := Za) (Zb := Zb) (Q := Q)
      hGram_meas hGram hQaa hQ ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact ae_of_all μ fun ω => by
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact twoSLSSubsetResidualizedScoreMapStar_eq_fromGram_sampleGram
      (stackRegressors Za m ω) (stackRegressors Zb m ω)

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [DecidableEq la] [DecidableEq lb] in
private theorem popGram_fullInstrument_submatrix_inl_inl
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (hZa : Integrable (fun ω => Matrix.vecMulVec (Za 0 ω) (Za 0 ω)) μ)
    (hZfull : Integrable
      (fun ω =>
        Matrix.vecMulVec
          (Sum.elim (Za 0 ω) (Zb 0 ω))
          (Sum.elim (Za 0 ω) (Zb 0 ω))) μ) :
    (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))).submatrix Sum.inl Sum.inl =
      popGram μ Za := by
  ext a b
  rw [popGram, popGram]
  calc
    (∫ ω, Matrix.vecMulVec (Sum.elim (Za 0 ω) (Zb 0 ω))
          (Sum.elim (Za 0 ω) (Zb 0 ω)) ∂μ) (Sum.inl a) (Sum.inl b)
        = ∫ ω,
            Matrix.vecMulVec (Sum.elim (Za 0 ω) (Zb 0 ω))
              (Sum.elim (Za 0 ω) (Zb 0 ω)) (Sum.inl a) (Sum.inl b) ∂μ := by
          exact integral_apply_apply hZfull (Sum.inl a) (Sum.inl b)
    _ = ∫ ω, Matrix.vecMulVec (Za 0 ω) (Za 0 ω) a b ∂μ := by
          simp [Matrix.vecMulVec_apply]
    _ = (∫ ω, Matrix.vecMulVec (Za 0 ω) (Za 0 ω) ∂μ) a b := by
          exact (integral_apply_apply hZa a b).symm

omit [Fintype k] [DecidableEq k] in
/-- The full-instrument projection fixes the residualized excluded-instrument
block on the nonsingular maintained/full instrument branch. -/
theorem instrumentProjectionStar_fromCols_mul_twoSLSSubsetResidualizedInstrumentsStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)] :
    instrumentProjectionStar (Matrix.fromCols Za Zb) *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb =
      twoSLSSubsetResidualizedInstrumentsStar Za Zb := by
  let Z := Matrix.fromCols Za Zb
  let PZ := instrumentProjectionStar Z
  let Pa := instrumentProjectionStar Za
  have hPZ_Z : PZ * Z = Z := by
    simpa [PZ, Z] using instrumentProjectionStar_mul_Z_of_nonsingular
      (Matrix.fromCols Za Zb)
  have hPZ_Za : PZ * Za = Za := by
    ext i a
    have h := congrArg (fun M : Matrix n (la ⊕ lb) ℝ => M i (Sum.inl a)) hPZ_Z
    simpa [Z, Matrix.mul_fromCols] using h
  have hPZ_Zb : PZ * Zb = Zb := by
    ext i b
    have h := congrArg (fun M : Matrix n (la ⊕ lb) ℝ => M i (Sum.inr b)) hPZ_Z
    simpa [Z, Matrix.mul_fromCols] using h
  have hPa_expand : Pa = Za * (Zaᵀ * Za)⁻¹ * Zaᵀ := by
    dsimp [Pa, instrumentProjectionStar]
  have hPZ_Pa : PZ * Pa = Pa := by
    calc
      PZ * Pa = PZ * (Za * (Zaᵀ * Za)⁻¹ * Zaᵀ) := by rw [hPa_expand]
      _ = (PZ * Za) * (Zaᵀ * Za)⁻¹ * Zaᵀ := by simp [Matrix.mul_assoc]
      _ = Za * (Zaᵀ * Za)⁻¹ * Zaᵀ := by rw [hPZ_Za]
      _ = Pa := hPa_expand.symm
  change
    PZ * (((1 : Matrix n n ℝ) - Pa) * Zb) =
      ((1 : Matrix n n ℝ) - Pa) * Zb
  calc
    PZ * (((1 : Matrix n n ℝ) - Pa) * Zb) =
        (PZ * ((1 : Matrix n n ℝ) - Pa)) * Zb := by rw [Matrix.mul_assoc]
    _ = (PZ - PZ * Pa) * Zb := by rw [Matrix.mul_sub, Matrix.mul_one]
    _ = (PZ - Pa) * Zb := by rw [hPZ_Pa]
    _ = PZ * Zb - Pa * Zb := by rw [Matrix.sub_mul]
    _ = Zb - Pa * Zb := by rw [hPZ_Zb]
    _ = ((1 : Matrix n n ℝ) - Pa) * Zb := by rw [Matrix.sub_mul, Matrix.one_mul]

/-- The residualized subset score is the explicit residualized-score map
applied to the full-instrument residual score.

This is the finite-sample algebraic bridge used to obtain the subset-score CLT
from the full Sargan residual-score CLT. -/
theorem twoSLSSubsetResidualizedScoreStar_eq_scoreMap_mul_sarganResidualScoreStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)] :
    twoSLSSubsetResidualizedScoreStar Za Zb X Y =
      twoSLSSubsetResidualizedScoreMapStar Za Zb *ᵥ
        twoSLSSarganResidualScoreStar (Matrix.fromCols Za Zb) X Y := by
  let Z := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let PZ := instrumentProjectionStar Z
  have hPZR : PZ * R = R := by
    simpa [PZ, Z, R] using
      instrumentProjectionStar_fromCols_mul_twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hPZsymm : PZᵀ = PZ := by
    simpa [PZ, Z] using instrumentProjectionStar_transpose_of_nonsingular
      (Matrix.fromCols Za Zb)
  have hRtPZ : Rᵀ * PZ = Rᵀ := by
    have hT := congrArg Matrix.transpose hPZR
    simpa [Matrix.transpose_mul, hPZsymm] using hT
  symm
  change
    (Rᵀ * Z * (Zᵀ * Z)⁻¹) *ᵥ
        (Zᵀ *ᵥ twoSLSResidualStar Z X Y) =
      Rᵀ *ᵥ twoSLSResidualStar Z X Y
  calc
    (Rᵀ * Z * (Zᵀ * Z)⁻¹) *ᵥ
        (Zᵀ *ᵥ twoSLSResidualStar Z X Y) =
        (Rᵀ * (Z * (Zᵀ * Z)⁻¹) * Zᵀ) *ᵥ
          twoSLSResidualStar Z X Y := by
          simp [Matrix.mul_assoc, Matrix.mulVec_mulVec]
    _ = (Rᵀ * PZ) *ᵥ twoSLSResidualStar Z X Y := by
          dsimp [PZ, instrumentProjectionStar]
          simp [Matrix.mul_assoc]
    _ = Rᵀ *ᵥ twoSLSResidualStar Z X Y := by rw [hRtPZ]

omit [Fintype k] [DecidableEq k] in
private theorem twoSLSSubsetResidualizedScoreMapStar_mul_fromCols_transpose
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)] :
    twoSLSSubsetResidualizedScoreMapStar Za Zb * (Matrix.fromCols Za Zb)ᵀ =
      (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ := by
  let Z := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let PZ := instrumentProjectionStar Z
  have hPZR : PZ * R = R := by
    simpa [PZ, Z, R] using
      instrumentProjectionStar_fromCols_mul_twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hPZsymm : PZᵀ = PZ := by
    simpa [PZ, Z] using instrumentProjectionStar_transpose_of_nonsingular
      (Matrix.fromCols Za Zb)
  have hRtPZ : Rᵀ * PZ = Rᵀ := by
    have hT := congrArg Matrix.transpose hPZR
    simpa [Matrix.transpose_mul, hPZsymm] using hT
  change (Rᵀ * Z * (Zᵀ * Z)⁻¹) * Zᵀ = Rᵀ
  calc
    (Rᵀ * Z * (Zᵀ * Z)⁻¹) * Zᵀ =
        Rᵀ * (Z * (Zᵀ * Z)⁻¹ * Zᵀ) := by
          simp [Matrix.mul_assoc]
    _ = Rᵀ * PZ := by rfl
    _ = Rᵀ := hRtPZ

omit [Fintype k] [DecidableEq k] in
private theorem twoSLSSubsetResidualizedScoreMapStar_sampleQZZ_mul_transpose
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)] :
    twoSLSSubsetResidualizedScoreMapStar Za Zb *
        sampleQZZ (Matrix.fromCols Za Zb) *
        (twoSLSSubsetResidualizedScoreMapStar Za Zb)ᵀ =
      (Fintype.card n : ℝ)⁻¹ •
        ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb) := by
  let Z := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let A := twoSLSSubsetResidualizedScoreMapStar Za Zb
  have hAZt : A * Zᵀ = Rᵀ := by
    simpa [A, Z, R] using
      twoSLSSubsetResidualizedScoreMapStar_mul_fromCols_transpose Za Zb
  have hZA_t : Z * Aᵀ = R := by
    have hT := congrArg Matrix.transpose hAZt
    simpa [Matrix.transpose_mul] using hT
  calc
    A * sampleQZZ Z * Aᵀ =
        A * ((Fintype.card n : ℝ)⁻¹ • (Zᵀ * Z)) * Aᵀ := by
          rfl
    _ = (Fintype.card n : ℝ)⁻¹ • ((A * Zᵀ) * (Z * Aᵀ)) := by
          simp [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
    _ = (Fintype.card n : ℝ)⁻¹ • (Rᵀ * R) := by
          rw [hAZt, hZA_t]

omit [Fintype k] [DecidableEq k] in
private theorem twoSLSSubsetResidualizedScoreMapStar_sampleQZX
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)] :
    twoSLSSubsetResidualizedScoreMapStar Za Zb *
        sampleQZX (Matrix.fromCols Za Zb) X =
      (Fintype.card n : ℝ)⁻¹ •
        ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X) := by
  let Z := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let A := twoSLSSubsetResidualizedScoreMapStar Za Zb
  let PZ := instrumentProjectionStar Z
  let Xhat := fittedRegressorsStar Z X
  have hAZt : A * Zᵀ = Rᵀ := by
    simpa [A, Z, R] using
      twoSLSSubsetResidualizedScoreMapStar_mul_fromCols_transpose Za Zb
  have hPZR : PZ * R = R := by
    simpa [PZ, Z, R] using
      instrumentProjectionStar_fromCols_mul_twoSLSSubsetResidualizedInstrumentsStar Za Zb
  have hPZsymm : PZᵀ = PZ := by
    simpa [PZ, Z] using instrumentProjectionStar_transpose_of_nonsingular
      (Matrix.fromCols Za Zb)
  have hRtPZ : Rᵀ * PZ = Rᵀ := by
    have hT := congrArg Matrix.transpose hPZR
    simpa [Matrix.transpose_mul, hPZsymm] using hT
  have hRX : Rᵀ * X = Rᵀ * Xhat := by
    calc
      Rᵀ * X = (Rᵀ * PZ) * X := by rw [hRtPZ]
      _ = Rᵀ * (PZ * X) := by rw [Matrix.mul_assoc]
      _ = Rᵀ * Xhat := by rfl
  calc
    A * sampleQZX Z X = A * ((Fintype.card n : ℝ)⁻¹ • (Zᵀ * X)) := by
      rfl
    _ = (Fintype.card n : ℝ)⁻¹ • ((A * Zᵀ) * X) := by
      simp [Matrix.mul_assoc, Matrix.mul_smul]
    _ = (Fintype.card n : ℝ)⁻¹ • (Rᵀ * Xhat) := by
      rw [hAZt, hRX]

omit [Fintype k] [DecidableEq k] in
private theorem sampleQXZ_mul_twoSLSSubsetResidualizedScoreMapStar_transpose
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)] :
    sampleQXZ (Matrix.fromCols Za Zb) X *
        (twoSLSSubsetResidualizedScoreMapStar Za Zb)ᵀ =
      (Fintype.card n : ℝ)⁻¹ •
        ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb) := by
  have h := twoSLSSubsetResidualizedScoreMapStar_sampleQZX Za Zb X
  have hT := congrArg Matrix.transpose h
  simpa [Matrix.transpose_mul, sampleQXZ, Matrix.transpose_smul] using hT

omit [DecidableEq n] [Fintype k] [DecidableEq k] in
private theorem fittedRegressorsStar_transpose_mul_self_eq_twoSLSMomentMatrixStar
    (Z : Matrix n (la ⊕ lb) ℝ) (X : Matrix n k ℝ)
    [Invertible (Zᵀ * Z)] :
    (fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X =
      twoSLSMomentMatrixStar Z X := by
  let PZ := instrumentProjectionStar Z
  have hPX :
      PZ * (PZ * X) = PZ * X := by
    rw [← Matrix.mul_assoc, instrumentProjectionStar_idempotent_of_nonsingular]
  unfold fittedRegressorsStar twoSLSMomentMatrixStar
  rw [Matrix.transpose_mul, instrumentProjectionStar_transpose_of_nonsingular]
  simpa [PZ, Matrix.mul_assoc] using
    congrArg (fun M : Matrix n k ℝ => Xᵀ * M) hPX

omit [DecidableEq n] [Fintype k] [DecidableEq k] in
private theorem fittedRegressorsStar_transpose_mul_self_eq_twoSLSMomentMatrixStar_generic
    {p : Type*} [Fintype p] [DecidableEq p]
    (Z : Matrix n p ℝ) (X : Matrix n k ℝ)
    [Invertible (Zᵀ * Z)] :
    (fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X =
      twoSLSMomentMatrixStar Z X := by
  let PZ := instrumentProjectionStar Z
  have hPX : PZ * (PZ * X) = PZ * X := by
    rw [← Matrix.mul_assoc, instrumentProjectionStar_idempotent_of_nonsingular]
  unfold fittedRegressorsStar twoSLSMomentMatrixStar
  rw [Matrix.transpose_mul, instrumentProjectionStar_transpose_of_nonsingular]
  simpa [PZ, Matrix.mul_assoc] using
    congrArg (fun M : Matrix n k ℝ => Xᵀ * M) hPX

omit [DecidableEq n] in
private theorem twoSLSBread_sample_inv_eq_card_smul_fittedRegressorsStar_gram_inv
    (Z : Matrix n (la ⊕ lb) ℝ) (X : Matrix n k ℝ) [Nonempty n]
    [Invertible (Zᵀ * Z)] :
    (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X))⁻¹ =
      (Fintype.card n : ℝ) •
        ((fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X)⁻¹ := by
  have hbread :=
    twoSLSBread_sample_eq_card_inv_smul_momentMatrixStar Z X
  have hgram :=
    fittedRegressorsStar_transpose_mul_self_eq_twoSLSMomentMatrixStar
      (Z := Z) (X := X)
  rw [hbread, hgram.symm, nonsingInv_smul]
  simp

private theorem twoSLSSubsetResidualizedScoreMapStar_sampleQZX_bread_sampleQXZ_mul_transpose
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ) [Nonempty n]
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)] :
    twoSLSSubsetResidualizedScoreMapStar Za Zb *
        (sampleQZX (Matrix.fromCols Za Zb) X *
          (twoSLSBread (sampleQXZ (Matrix.fromCols Za Zb) X)
            (sampleQZZ (Matrix.fromCols Za Zb))
            (sampleQZX (Matrix.fromCols Za Zb) X))⁻¹ *
          sampleQXZ (Matrix.fromCols Za Zb) X) *
        (twoSLSSubsetResidualizedScoreMapStar Za Zb)ᵀ =
      (Fintype.card n : ℝ)⁻¹ •
        ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X *
          ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
            fittedRegressorsStar (Matrix.fromCols Za Zb) X)⁻¹ *
          (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb) := by
  let Z := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let A := twoSLSSubsetResidualizedScoreMapStar Za Zb
  let Xhat := fittedRegressorsStar Z X
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  have hN : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hAQZX : A * sampleQZX Z X = c • (Rᵀ * Xhat) := by
    simpa [A, Z, R, Xhat, c] using
      twoSLSSubsetResidualizedScoreMapStar_sampleQZX Za Zb X
  have hQXZA : sampleQXZ Z X * Aᵀ = c • (Xhatᵀ * R) := by
    simpa [A, Z, R, Xhat, c] using
      sampleQXZ_mul_twoSLSSubsetResidualizedScoreMapStar_transpose Za Zb X
  have hBreadInv :
      (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X))⁻¹ =
        (Fintype.card n : ℝ) • (Xhatᵀ * Xhat)⁻¹ := by
    simpa [Z, Xhat] using
      twoSLSBread_sample_inv_eq_card_smul_fittedRegressorsStar_gram_inv
        (Z := Z) (X := X)
  calc
    A * (sampleQZX Z X *
          (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X))⁻¹ *
          sampleQXZ Z X) * Aᵀ =
        (A * sampleQZX Z X) *
          (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X))⁻¹ *
          (sampleQXZ Z X * Aᵀ) := by
          simp [Matrix.mul_assoc]
    _ = (c • (Rᵀ * Xhat)) *
          ((Fintype.card n : ℝ) • (Xhatᵀ * Xhat)⁻¹) *
          (c • (Xhatᵀ * R)) := by
          rw [hAQZX, hBreadInv, hQXZA]
    _ = c • (Rᵀ * Xhat * (Xhatᵀ * Xhat)⁻¹ * Xhatᵀ * R) := by
          simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, c, hN, Matrix.mul_assoc]

omit [DecidableEq n] in
private theorem twoSLSOveridResidualMaker_mul_sampleQZZ
    (Z : Matrix n (la ⊕ lb) ℝ) (X : Matrix n k ℝ) [Nonempty n]
    [Invertible (Zᵀ * Z)] :
    twoSLSOveridResidualMaker Z X * sampleQZZ Z =
      sampleQZZ Z -
        sampleQZX Z X *
          (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X))⁻¹ *
          sampleQXZ Z X := by
  have hN : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hQunit : IsUnit (sampleQZZ Z).det := by
    rw [sampleQZZ, sampleGram, isUnit_iff_ne_zero, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hN))
      (Matrix.isUnit_det_of_invertible (Zᵀ * Z)).ne_zero
  simp [twoSLSOveridResidualMaker, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul (sampleQZZ Z) hQunit]

/-- Normalized Newey middle matrix as the sample covariance of Hansen's
residualized full-instrument overidentification score.

This finite-sample identity is the covariance bridge for Hansen Theorem 12.17:
it rewrites `n⁻¹` times Newey's residualized-instrument middle matrix into the
sample residual-maker covariance form used by the full Sargan statistic. -/
theorem twoSLSSubsetNeweyMiddleStar_card_inv_smul_eq_scoreMap_overidResidualMaker_sampleQZZ
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ) [Nonempty n]
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)] :
    (Fintype.card n : ℝ)⁻¹ • twoSLSSubsetNeweyMiddleStar Za Zb X =
      let Z : Matrix n (la ⊕ lb) ℝ := Matrix.fromCols Za Zb
      let A : Matrix lb (la ⊕ lb) ℝ := twoSLSSubsetResidualizedScoreMapStar Za Zb
      A * (twoSLSOveridResidualMaker Z X * sampleQZZ Z) * Aᵀ := by
  let Z : Matrix n (la ⊕ lb) ℝ := Matrix.fromCols Za Zb
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let A : Matrix lb (la ⊕ lb) ℝ := twoSLSSubsetResidualizedScoreMapStar Za Zb
  let Xhat := fittedRegressorsStar Z X
  let B :=
    sampleQZX Z X *
      (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X))⁻¹ *
      sampleQXZ Z X
  have hGram :
      A * sampleQZZ Z * Aᵀ =
        (Fintype.card n : ℝ)⁻¹ • (Rᵀ * R) := by
    simpa [A, Z, R] using
      twoSLSSubsetResidualizedScoreMapStar_sampleQZZ_mul_transpose Za Zb
  have hCorr :
      A * B * Aᵀ =
        (Fintype.card n : ℝ)⁻¹ •
          (Rᵀ * Xhat * (Xhatᵀ * Xhat)⁻¹ * Xhatᵀ * R) := by
    simpa [A, Z, R, Xhat, B, Matrix.mul_assoc] using
      twoSLSSubsetResidualizedScoreMapStar_sampleQZX_bread_sampleQXZ_mul_transpose
        Za Zb X
  have hMQ :
      twoSLSOveridResidualMaker Z X * sampleQZZ Z =
        sampleQZZ Z - B := by
    simpa [Z, B, Matrix.mul_assoc] using
      twoSLSOveridResidualMaker_mul_sampleQZZ (Z := Z) (X := X)
  calc
    (Fintype.card n : ℝ)⁻¹ • twoSLSSubsetNeweyMiddleStar Za Zb X =
        (Fintype.card n : ℝ)⁻¹ •
          (Rᵀ * R - Rᵀ * Xhat * (Xhatᵀ * Xhat)⁻¹ * Xhatᵀ * R) := by
          rfl
    _ = (Fintype.card n : ℝ)⁻¹ • (Rᵀ * R) -
        (Fintype.card n : ℝ)⁻¹ •
          (Rᵀ * Xhat * (Xhatᵀ * Xhat)⁻¹ * Xhatᵀ * R) := by
          rw [smul_sub]
    _ = A * sampleQZZ Z * Aᵀ - A * B * Aᵀ := by
          rw [hGram, hCorr]
    _ = A * (sampleQZZ Z - B) * Aᵀ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = A * (twoSLSOveridResidualMaker Z X * sampleQZZ Z) * Aᵀ := by
          rw [hMQ]

/-- Residualized-score map measurability from row measurability. -/
theorem twoSLSSubsetResidualizedScoreMapStar_aestronglyMeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (m : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)) μ := by
  let Rmat : Ω → Matrix (Fin m) lb ℝ := fun ω =>
    twoSLSSubsetResidualizedInstrumentsStar
      (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ := fun i ω =>
    Sum.elim (Za i ω) (Zb i ω)
  let Zmat : Ω → Matrix (Fin m) (la ⊕ lb) ℝ := fun ω =>
    fun i => Zfull i.val ω
  have hR : AEStronglyMeasurable Rmat μ :=
    twoSLSSubsetResidualizedInstrumentsStar_aestronglyMeasurable_of_rows
      (μ := μ) (Za := Za) (Zb := Zb) hZa hZb m
  have hRt : AEStronglyMeasurable (fun ω => (Rmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hR
  have hZfull : ∀ i, AEStronglyMeasurable (Zfull i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zfull i) ?_
    intro s
    cases s with
    | inl a =>
        exact (measurable_pi_apply a).comp_aemeasurable (hZa i).aemeasurable
    | inr b =>
        exact (measurable_pi_apply b).comp_aemeasurable (hZb i).aemeasurable
  have hZmat : AEStronglyMeasurable Zmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) (X := Zfull) hZfull
  have hZt : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZmat
  have hGram : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ * Zmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZt.prodMk hZmat)
  have hInv : AEStronglyMeasurable (fun ω => ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hLeft : AEStronglyMeasurable (fun ω => (Rmat ω)ᵀ * Zmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRt.prodMk hZmat)
  have hMap : AEStronglyMeasurable
      (fun ω => (Rmat ω)ᵀ * Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hInv)
  simpa [twoSLSSubsetResidualizedScoreMapStar, Rmat, Zmat, Zfull, Matrix.fromCols,
    Matrix.mul_assoc] using hMap

/-- Residualized excluded-instrument score measurability from row
measurability. -/
theorem twoSLSSubsetResidualizedScoreStar_aestronglyMeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (m : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreStar
          (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ := by
  let Rmat : Ω → Matrix (Fin m) lb ℝ := fun ω =>
    twoSLSSubsetResidualizedInstrumentsStar
      (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
  let Zmat : ℕ → Ω → (la ⊕ lb) → ℝ := fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hR : AEStronglyMeasurable Rmat μ :=
    twoSLSSubsetResidualizedInstrumentsStar_aestronglyMeasurable_of_rows
      (μ := μ) (Za := Za) (Zb := Zb) hZa hZb m
  have hRt : AEStronglyMeasurable (fun ω => (Rmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hR
  have hZ : ∀ i, AEStronglyMeasurable (Zmat i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zmat i) ?_
    intro j
    cases j with
    | inl a =>
        exact (measurable_pi_apply a).comp_aemeasurable (hZa i).aemeasurable
    | inr b =>
        exact (measurable_pi_apply b).comp_aemeasurable (hZb i).aemeasurable
  have hres : AEStronglyMeasurable
      (fun ω =>
        twoSLSResidualStar
          (fun i : Fin m => Zmat i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    twoSLSResidualStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Zmat) (X := X) (Y := Y) hZ hX hY
  have hscore : AEStronglyMeasurable
      (fun ω => (Rmat ω)ᵀ *ᵥ
        twoSLSResidualStar
          (fun i : Fin m => Zmat i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRt.prodMk hres)
  simpa [twoSLSSubsetResidualizedScoreStar, Rmat, Zmat] using hscore

/-- Scaled residualized excluded-instrument score measurability from row
measurability. -/
theorem twoSLSSubsetResidualizedScoreStar_scaled_aemeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (m : ℕ) :
    AEMeasurable
      (fun ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
            (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
  ((twoSLSSubsetResidualizedScoreStar_aestronglyMeasurable_of_rows
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
    hZa hZb hX hY m).const_smul ((Real.sqrt (m : ℝ))⁻¹)).aemeasurable

/-- Criterion covariance estimate for Newey's residualized subset score. -/
noncomputable def twoSLSSubsetNeweyCriterionCovHatStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : Matrix lb lb ℝ :=
  let Z := Matrix.fromCols Za Zb
  twoSLSSigmaSqHatStar Z X Y •
    ((Fintype.card n : ℝ)⁻¹ • twoSLSSubsetNeweyMiddleStar Za Zb X)

/-- Population covariance target for Newey's residualized subset score in
Hansen Theorem 12.17.

This is the displayed linear-Gaussian covariance `(A M) Ω (A M)'`, where `A`
is the limiting residualized-score map, `M` is the full-instrument population
residual maker from Theorem 12.16, and `Ω = scoreCovMat μ [Za,Zb] e`. -/
noncomputable def twoSLSSubsetResidualizedScoreCovariance
    [MeasurableSpace Ω] (μ : Measure Ω)
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (A : Matrix lb (la ⊕ lb) ℝ) : Matrix lb lb ℝ :=
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
  let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let R : Matrix lb (la ⊕ lb) ℝ := A * M
  R * scoreCovMat μ Zfull e * Rᵀ

/-- Limiting residualized-score map in the displayed Newey covariance for
Hansen Theorem 12.17.  This names the map `A M` so full-row-rank side
conditions can be stated independently of the large covariance expression. -/
noncomputable def twoSLSSubsetLimitResidualizedScoreMap
    [MeasurableSpace Ω] (μ : Measure Ω)
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (A : Matrix lb (la ⊕ lb) ℝ) :
    Matrix lb (la ⊕ lb) ℝ :=
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
  let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  A * M

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] in
private theorem twoSLSSubsetResidualizedScoreMapFromGram_fullRowRank
    (Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ)
    (hQaa : IsUnit (Q.submatrix Sum.inl Sum.inl).det)
    (hQ : IsUnit Q.det) :
    Function.Injective
      (fun v : lb → ℝ =>
        Matrix.vecMul v (twoSLSSubsetResidualizedScoreMapFromGram Q)) := by
  classical
  let Qaa : Matrix la la ℝ := Q.submatrix Sum.inl Sum.inl
  let Qab : Matrix la lb ℝ := Q.submatrix Sum.inl Sum.inr
  let Qba : Matrix lb la ℝ := Q.submatrix Sum.inr Sum.inl
  let Qbb : Matrix lb lb ℝ := Q.submatrix Sum.inr Sum.inr
  let S : Matrix lb lb ℝ := Qbb - Qba * Qaa⁻¹ * Qab
  let A : Matrix lb (la ⊕ lb) ℝ :=
    twoSLSSubsetResidualizedScoreMapFromGram Q
  letI : Invertible Qaa :=
    Matrix.invertibleOfIsUnitDet (A := Qaa) (by simpa [Qaa] using hQaa)
  have hblocks : Matrix.fromBlocks Qaa Qab Qba Qbb = Q := by
    ext i j
    cases i <;> cases j <;> rfl
  have hS : IsUnit S := by
    have hQunit : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr hQ
    have hBlocksUnit : IsUnit (Matrix.fromBlocks Qaa Qab Qba Qbb) := by
      simpa [hblocks] using hQunit
    have hSchur :=
      (Matrix.isUnit_fromBlocks_iff_of_invertible₁₁
        (A := Qaa) (B := Qab) (C := Qba) (D := Qbb)).mp hBlocksUnit
    simpa [S, invOf_eq_nonsing_inv] using hSchur
  have hAQ : A * Q =
      Q.submatrix Sum.inr id -
        Qba * Qaa⁻¹ * Q.submatrix Sum.inl id := by
    dsimp [A, twoSLSSubsetResidualizedScoreMapFromGram]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hQ, Matrix.mul_one]
  have hAQ_right : (A * Q).submatrix id Sum.inr = S := by
    rw [hAQ]
    ext b c
    simp [S, Qaa, Qab, Qba, Qbb, Matrix.mul_apply]
  intro v w hvw
  have hAQv : Matrix.vecMul v (A * Q) = Matrix.vecMul w (A * Q) := by
    change Matrix.vecMul v A = Matrix.vecMul w A at hvw
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hvw]
  have hSv : Matrix.vecMul v S = Matrix.vecMul w S := by
    have hSub :
        Matrix.vecMul v ((A * Q).submatrix id Sum.inr) =
          Matrix.vecMul w ((A * Q).submatrix id Sum.inr) := by
      ext b
      exact congrFun hAQv (Sum.inr b)
    simpa [hAQ_right] using hSub
  exact Matrix.vecMul_injective_of_isUnit hS hSv

omit [Fintype n] [DecidableEq n] in
/-- Hansen's maintained first-stage rank prevents the full-model residual maker
from removing a nonzero row of the excluded-instrument residualization map. -/
theorem twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_partitioned_rank
    (QXZ : Matrix k (la ⊕ lb) ℝ) (QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ)
    (QZX : Matrix (la ⊕ lb) k ℝ)
    (hQXZ : QXZ = QZXᵀ)
    (hQaa : IsUnit (QZZ.submatrix Sum.inl Sum.inl).det)
    (hQZZ : IsUnit QZZ.det)
    (hMaintainedRank : Function.Injective
      (QZX.submatrix Sum.inl id).mulVec) :
    Function.Injective
      (fun v : lb → ℝ => Matrix.vecMul v
        (twoSLSSubsetResidualizedScoreMapFromGram QZZ *
          twoSLSOveridPopulationResidualMaker QXZ QZZ QZX)) := by
  classical
  let A : Matrix lb (la ⊕ lb) ℝ :=
    twoSLSSubsetResidualizedScoreMapFromGram QZZ
  let B : Matrix k k ℝ := twoSLSBread QXZ QZZ QZX
  let M : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let Qaa : Matrix la la ℝ := QZZ.submatrix Sum.inl Sum.inl
  let Qba : Matrix lb la ℝ := QZZ.submatrix Sum.inr Sum.inl
  have hA : Function.Injective (fun v : lb → ℝ => Matrix.vecMul v A) := by
    simpa [A] using
      twoSLSSubsetResidualizedScoreMapFromGram_fullRowRank QZZ hQaa hQZZ
  have hAQ : A * QZZ =
      QZZ.submatrix Sum.inr id -
        Qba * Qaa⁻¹ * QZZ.submatrix Sum.inl id := by
    dsimp [A, Qaa, Qba, twoSLSSubsetResidualizedScoreMapFromGram]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul QZZ hQZZ, Matrix.mul_one]
  have hCorrection : Qba * Qaa⁻¹ * Qaa = Qba := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Qaa (by simpa [Qaa] using hQaa),
      Matrix.mul_one]
  have hAQ_left : (A * QZZ).submatrix id Sum.inl = 0 := by
    rw [hAQ]
    ext b a
    change Qba b a - (Qba * Qaa⁻¹ * Qaa) b a = 0
    rw [hCorrection]
    simp
  intro v w hvw
  let d : lb → ℝ := v - w
  have hdAM : Matrix.vecMul d (A * M) = 0 := by
    rw [Matrix.sub_vecMul]
    change Matrix.vecMul v (A * M) - Matrix.vecMul w (A * M) = 0
    simpa [A, M] using sub_eq_zero.mpr hvw
  let u : (la ⊕ lb) → ℝ := Matrix.vecMul d A
  have huM : Matrix.vecMul u M = 0 := by
    simpa [u, Matrix.vecMul_vecMul] using hdAM
  let t : k → ℝ := Matrix.vecMul (Matrix.vecMul u QZX) B⁻¹
  have hu_eq : u = Matrix.vecMul t (QXZ * QZZ⁻¹) := by
    have huM' :
        Matrix.vecMul u
          ((1 : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) -
            QZX * B⁻¹ * QXZ * QZZ⁻¹) = 0 := by
      simpa [M, B, twoSLSOveridPopulationResidualMaker] using huM
    rw [Matrix.vecMul_sub, Matrix.vecMul_one] at huM'
    have hu := sub_eq_zero.mp huM'
    simpa [t, Matrix.vecMul_vecMul, Matrix.mul_assoc] using hu
  have huQ : Matrix.vecMul u QZZ = Matrix.vecMul t QXZ := by
    rw [hu_eq, Matrix.vecMul_vecMul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul QZZ hQZZ, Matrix.mul_one]
  have huQ_left : (Matrix.vecMul u QZZ) ∘ Sum.inl = 0 := by
    funext a
    have hz : Matrix.vecMul d ((A * QZZ).submatrix id Sum.inl) = 0 := by
      rw [hAQ_left]
      simp
    change Matrix.vecMul u QZZ (Sum.inl a) = 0
    calc
      Matrix.vecMul u QZZ (Sum.inl a) =
          Matrix.vecMul d (A * QZZ) (Sum.inl a) := by
            dsimp [u]
            rw [Matrix.vecMul_vecMul]
      _ = Matrix.vecMul d ((A * QZZ).submatrix id Sum.inl) a := rfl
      _ = 0 := congrFun hz a
  have htQXZ_left : (Matrix.vecMul t QXZ) ∘ Sum.inl = 0 := by
    rw [← huQ]
    exact huQ_left
  have hMaintainedZero : (QZX.submatrix Sum.inl id) *ᵥ t = 0 := by
    funext a
    have ha := congrFun htQXZ_left a
    simpa [hQXZ, Matrix.mulVec, Matrix.vecMul, Matrix.transpose_apply,
      Matrix.submatrix_apply] using ha
  have ht : t = 0 := hMaintainedRank (by simpa using hMaintainedZero)
  have hu : u = 0 := by
    rw [ht] at hu_eq
    simpa using hu_eq
  have hd : d = 0 := hA (by simpa [u] using hu)
  exact sub_eq_zero.mp (by simpa [d] using hd)

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq la]
    [DecidableEq lb] in
private theorem twoSLSCombinedQZX_fullInstrument_submatrix_inl
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ)
    (hMaintained : Integrable (fun ω =>
      Matrix.vecMulVec (twoSLSCombinedRegressors Za X 0 ω)
        (twoSLSCombinedRegressors Za X 0 ω)) μ)
    (hFull : Integrable (fun ω =>
      Matrix.vecMulVec
        (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X 0 ω)
        (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X 0 ω)) μ) :
    (twoSLSCombinedQZX
      (popGram μ (twoSLSCombinedRegressors
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))).submatrix Sum.inl id =
      twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Za X)) := by
  ext a j
  rw [twoSLSCombinedQZX, twoSLSCombinedQZX, popGram, popGram]
  calc
    (∫ ω,
        Matrix.vecMulVec
          (twoSLSCombinedRegressors
            (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X 0 ω)
          (twoSLSCombinedRegressors
            (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X 0 ω) ∂μ)
          (Sum.inl (Sum.inl a)) (Sum.inr j) =
        ∫ ω,
          Matrix.vecMulVec
            (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X 0 ω)
            (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X 0 ω)
            (Sum.inl (Sum.inl a)) (Sum.inr j) ∂μ :=
      integral_apply_apply hFull (Sum.inl (Sum.inl a)) (Sum.inr j)
    _ = ∫ ω,
          Matrix.vecMulVec (twoSLSCombinedRegressors Za X 0 ω)
            (twoSLSCombinedRegressors Za X 0 ω)
            (Sum.inl a) (Sum.inr j) ∂μ := by
      simp [twoSLSCombinedRegressors, Matrix.vecMulVec_apply]
    _ = (∫ ω,
          Matrix.vecMulVec (twoSLSCombinedRegressors Za X 0 ω)
            (twoSLSCombinedRegressors Za X 0 ω) ∂μ)
          (Sum.inl a) (Sum.inr j) :=
      (integral_apply_apply hMaintained (Sum.inl a) (Sum.inr j)).symm

set_option linter.style.longLine false in
/-- The maintained/full Assumption 12.2 population rank conditions derive the
full-row-rank limiting excluded-instrument score map. -/
theorem twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_assumption12_2_partitioned
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (hMaintained : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e) :
    Function.Injective
      (fun v : lb → ℝ => Matrix.vecMul v
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X
          (twoSLSSubsetResidualizedScoreMapFromGram
            (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)))))) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let hMaintainedGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Za X e :=
    hMaintained.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions.toGramConditions
  let hFullGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Zfull X e :=
    hFull.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions.toGramConditions
  have hZaInt : Integrable (fun ω => Matrix.vecMulVec (Za 0 ω) (Za 0 ω)) μ :=
    hMaintainedGram.instrument_moments.int_outer
  have hFullInt : Integrable (fun ω =>
      Matrix.vecMulVec (Zfull 0 ω) (Zfull 0 ω)) μ :=
    hFullGram.instrument_moments.int_outer
  have hMaintainedCombinedInt : Integrable (fun ω =>
      Matrix.vecMulVec (twoSLSCombinedRegressors Za X 0 ω)
        (twoSLSCombinedRegressors Za X 0 ω)) μ :=
    hMaintainedGram.combined_gram.int_outer
  have hFullCombinedInt : Integrable (fun ω =>
      Matrix.vecMulVec (twoSLSCombinedRegressors Zfull X 0 ω)
        (twoSLSCombinedRegressors Zfull X 0 ω)) μ :=
    hFullGram.combined_gram.int_outer
  have hQeq : popGram μ Zfull =
      twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X)) :=
    popGram_eq_twoSLSCombinedQZZ_popGram hFullInt hFullCombinedInt
  have hQaa : IsUnit
      ((twoSLSCombinedQZZ
        (popGram μ (twoSLSCombinedRegressors Zfull X))).submatrix
          Sum.inl Sum.inl).det := by
    rw [← hQeq, popGram_fullInstrument_submatrix_inl_inl
      (μ := μ) Za Zb hZaInt hFullInt]
    have hMaintainedIid :=
      hMaintained.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions.toTwoSLSSplitIidSecondMomentRankConditions
    exact hMaintainedIid.instrument_popGram_nonsing
  have hQXZ :
      twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X)) =
        (twoSLSCombinedQZX
          (popGram μ (twoSLSCombinedRegressors Zfull X)))ᵀ :=
    twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
      (μ := μ) (Z := Zfull) (X := X) hFullGram.combined_gram
  have hMaintainedRank : Function.Injective
      ((twoSLSCombinedQZX
        (popGram μ (twoSLSCombinedRegressors Zfull X))).submatrix
          Sum.inl id).mulVec := by
    rw [twoSLSCombinedQZX_fullInstrument_submatrix_inl
      (μ := μ) Za Zb X hMaintainedCombinedInt hFullCombinedInt]
    exact hMaintained.qzx_rank
  have hRank :=
    twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_partitioned_rank
      (QXZ := twoSLSCombinedQXZ
        (popGram μ (twoSLSCombinedRegressors Zfull X)))
      (QZZ := twoSLSCombinedQZZ
        (popGram μ (twoSLSCombinedRegressors Zfull X)))
      (QZX := twoSLSCombinedQZX
        (popGram μ (twoSLSCombinedRegressors Zfull X)))
      hQXZ hQaa
      ((Matrix.isUnit_iff_isUnit_det _).mp hFull.qzz_posDef.isUnit)
      hMaintainedRank
  simpa [twoSLSSubsetLimitResidualizedScoreMap, Zfull, hQeq] using hRank

set_option linter.style.longLine false in
/-- Population-rank version of the limiting row-Gram certificate in Hansen
Theorem 12.17. -/
theorem twoSLSSubsetLimitResidualizedScoreMap_rowGram_det_isUnit_of_assumption12_2_partitioned
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (hMaintained : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e) :
    IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X
          (twoSLSSubsetResidualizedScoreMapFromGram
            (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X
          (twoSLSSubsetResidualizedScoreMapFromGram
            (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)))))ᵀ).det := by
  let R : Matrix lb (la ⊕ lb) ℝ :=
    twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X
      (twoSLSSubsetResidualizedScoreMapFromGram
        (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))
  have hR : Function.Injective (fun v : lb → ℝ => Matrix.vecMul v R) := by
    simpa [R] using
      twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_assumption12_2_partitioned
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e)
        hMaintained hFull
  have hPos : (R * Rᵀ).PosDef := by
    have h := Matrix.PosDef.mul_mul_conjTranspose_same
      (Matrix.PosDef.one (n := la ⊕ lb) (R := ℝ)) hR
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  exact (Matrix.isUnit_iff_isUnit_det _).mp hPos.isUnit

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 derives the limiting row-Gram certificate;
no separate row-Gram or covariance-target rank premise is needed. -/
theorem twoSLSSubsetLimitResidualizedScoreMap_rowGram_det_isUnit_of_observed_assumption12_2
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β) :
    IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X
          (twoSLSSubsetResidualizedScoreMapFromGram
            (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X
          (twoSLSSubsetResidualizedScoreMapFromGram
            (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)))))ᵀ).det :=
  twoSLSSubsetLimitResidualizedScoreMap_rowGram_det_isUnit_of_assumption12_2_partitioned
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e)
    hMaintained.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
    hFull.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions

private theorem matrix_vecMul_injective_of_rowGram_det_isUnit
    {r c : Type*} [Fintype r] [DecidableEq r] [Fintype c]
    (R : Matrix r c ℝ) (hGram : IsUnit (R * Rᵀ).det) :
    Function.Injective (fun v : r → ℝ => Matrix.vecMul v R) := by
  have hUnit : IsUnit (R * Rᵀ) :=
    (Matrix.isUnit_iff_isUnit_det (R * Rᵀ)).mpr hGram
  have hInj : Function.Injective (fun v : r → ℝ => Matrix.vecMul v (R * Rᵀ)) :=
    Matrix.vecMul_injective_of_isUnit hUnit
  intro v w hv
  apply hInj
  calc
    Matrix.vecMul v (R * Rᵀ) = Matrix.vecMul (Matrix.vecMul v R) Rᵀ := by
      rw [Matrix.vecMul_vecMul]
    _ = Matrix.vecMul (Matrix.vecMul w R) Rᵀ :=
      congrArg (fun u => Matrix.vecMul u Rᵀ) hv
    _ = Matrix.vecMul w (R * Rᵀ) := by
      rw [Matrix.vecMul_vecMul]

/-- A nonsingular row Gram for the limiting residualized-score map gives the
full-row-rank condition used in Hansen Theorem 12.17 covariance bridges. -/
theorem twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
    [MeasurableSpace Ω] (μ : Measure Ω)
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (A : Matrix lb (la ⊕ lb) ℝ)
    (hGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    Function.Injective
      (fun v : lb → ℝ =>
        Matrix.vecMul v (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)) :=
  matrix_vecMul_injective_of_rowGram_det_isUnit
    (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) hGram

/-- Positive-definite row-Gram version of
`twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit`.
This matches the regularity form often used when Hansen's residualized-score
map is checked through a displayed positive-definite Gram matrix. -/
theorem twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_posDef
    [MeasurableSpace Ω] (μ : Measure Ω)
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (A : Matrix lb (la ⊕ lb) ℝ)
    (hGram :
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).PosDef) :
    Function.Injective
      (fun v : lb → ℝ =>
        Matrix.vecMul v (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)) := by
  have hGram_det : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hGram.isUnit
  exact
    twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
      μ Za Zb X A hGram_det

set_option linter.style.longLine false in
/-- The displayed Newey subset covariance is positive definite when Hansen's
full residual-score covariance is positive definite and the limiting
residualized-score map has full row rank. -/
theorem twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_fullRowRank
    [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (hR_fullRowRank : Function.Injective
      (fun v : lb → ℝ =>
        Matrix.vecMul v (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A))) :
    (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A).PosDef := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let R : Matrix lb (la ⊕ lb) ℝ :=
    twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A
  let S : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := scoreCovMat μ Zfull e
  have hS : S.PosDef := by
    simpa [S, Zfull] using hFull.omega_posDef
  have hR_inj : Function.Injective (fun v : lb → ℝ => Matrix.vecMul v R) := by
    simpa [R] using hR_fullRowRank
  have hRpos : (R * S * R.conjTranspose).PosDef :=
    Matrix.PosDef.mul_mul_conjTranspose_same hS hR_inj
  have hCov :
      twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A = R * S * Rᵀ := by
    simp [twoSLSSubsetResidualizedScoreCovariance,
      twoSLSSubsetLimitResidualizedScoreMap, Zfull, R, S, Matrix.mul_assoc]
  rw [hCov]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hRpos

/-- Row-Gram version of
`twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_fullRowRank`. -/
theorem twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_rowGram
    [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (hGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A).PosDef :=
  twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_fullRowRank
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (A := A)
    hFull
    (twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
      μ Za Zb X A hGram)

/-- Positive-definite row-Gram version of
`twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_rowGram`. -/
theorem twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_rowGram_posDef
    [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (hGram :
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).PosDef) :
    (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A).PosDef :=
  twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_fullRowRank
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (A := A)
    hFull
    (twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_posDef
      μ Za Zb X A hGram)

set_option linter.style.longLine false in
/-- In the homoskedastic case, the displayed residualized-score covariance
equals the Newey CMT target `σ² A(M Q_ZZ)A'`.

The proof reuses the population residual-maker idempotence and weighted
self-adjointness already used for Hansen Theorem 12.16. -/
theorem twoSLSSubsetResidualizedScoreCovariance_eq_sigma_scoreMap_residualMaker_popGram
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {sigma2 : ℝ}
    (hQXZ :
      twoSLSCombinedQXZ
          (popGram μ (twoSLSCombinedRegressors
            (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)) =
        (twoSLSCombinedQZX
          (popGram μ (twoSLSCombinedRegressors
            (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))ᵀ)
    (hQZZ_pos :
      (twoSLSCombinedQZZ
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))).PosDef)
    (hBread_unit :
      IsUnit
        (twoSLSBread
          (twoSLSCombinedQXZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
          (twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
          (twoSLSCombinedQZX
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))).det)
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        sigma2 •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))) :
    twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A =
      sigma2 •
        (A *
          (twoSLSOveridPopulationResidualMaker
            (twoSLSCombinedQXZ
              (popGram μ (twoSLSCombinedRegressors
                (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
            (twoSLSCombinedQZZ
              (popGram μ (twoSLSCombinedRegressors
                (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
            (twoSLSCombinedQZX
              (popGram μ (twoSLSCombinedRegressors
                (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))) *
              twoSLSCombinedQZZ
                (popGram μ (twoSLSCombinedRegressors
                  (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))) * Aᵀ) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let QXZ : Matrix k (la ⊕ lb) ℝ :=
    twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZX : Matrix (la ⊕ lb) k ℝ :=
    twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
  let M : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  have hQXZ' : QXZ = QZXᵀ := by
    simpa [Zfull, QXZ, QZX] using hQXZ
  have hQZZ_pos' : QZZ.PosDef := by
    simpa [Zfull, QZZ] using hQZZ_pos
  have hQZZ_symm : QZZᵀ = QZZ := by
    have hHerm : QZZ.IsHermitian := hQZZ_pos'.isHermitian
    simpa [Matrix.conjTranspose] using hHerm.eq
  have hQZZ_unit : IsUnit QZZ.det :=
    (Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ_pos'.isUnit
  have hMidem : IsIdempotentElem M := by
    simpa [M, QXZ, QZZ, QZX, Zfull] using
      twoSLSOveridPopulationResidualMaker_idempotent hBread_unit
  have hMself : M * QZZ = QZZ * Mᵀ := by
    simpa [M, QXZ, QZZ, QZX] using
      twoSLSOveridPopulationResidualMaker_weighted_selfAdjoint
        hQXZ' hQZZ_symm hQZZ_unit
  have hMQMt : M * QZZ * Mᵀ = M * QZZ := by
    have hMM : M * M = M := by
      simpa [IsIdempotentElem] using hMidem
    calc
      M * QZZ * Mᵀ = (QZZ * Mᵀ) * Mᵀ := by rw [hMself]
      _ = QZZ * (Mᵀ * Mᵀ) := by simp [Matrix.mul_assoc]
      _ = QZZ * (M * M)ᵀ := by rw [Matrix.transpose_mul]
      _ = QZZ * Mᵀ := by rw [hMM]
      _ = M * QZZ := hMself.symm
  have hcov' : scoreCovMat μ Zfull e = sigma2 • QZZ := by
    simpa [Zfull, QZZ] using hcov
  calc
    twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A =
        (A * M) * (sigma2 • QZZ) * (A * M)ᵀ := by
          simp [twoSLSSubsetResidualizedScoreCovariance, Zfull, QXZ, QZZ, QZX,
            M, hcov', Matrix.mul_assoc]
    _ = sigma2 • (A * (M * QZZ * Mᵀ) * Aᵀ) := by
          simp [Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = sigma2 • (A * (M * QZZ) * Aᵀ) := by
          rw [hMQMt]

/-- High-probability sample-rank conditions for Hansen Theorem 12.17.

Unlike `TwoSLSSubsetEventuallyRankConditions`, this package is implied by the
usual iid moment and population-rank assumptions even for discrete designs.
The two instrument-Gram branches and the two 2SLS-bread branches are exactly
the four nonsingularity facts used by the finite-sample `N = C*` identity. -/
structure TwoSLSSubsetRankFailureProbabilityConditions
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) : Prop where
  maintained_instrument : Tendsto
    (fun m => μ {ω | ¬ IsUnit
      (((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω).det)})
    atTop (𝓝 0)

  full_instrument : Tendsto
    (fun m => μ {ω | ¬ IsUnit
      (((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
        Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)).det)})
    atTop (𝓝 0)
  maintained_bread : Tendsto
    (fun m => μ {ω | ¬ IsUnit
      (twoSLSBread
        (sampleQXZ (stackRegressors Za m ω) (stackRegressors X m ω))
        (sampleQZZ (stackRegressors Za m ω))
        (sampleQZX (stackRegressors Za m ω) (stackRegressors X m ω))).det})
    atTop (𝓝 0)
  full_bread : Tendsto
    (fun m => μ {ω | ¬ IsUnit
      (twoSLSBread
        (sampleQXZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))
        (sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
        (sampleQZX
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))).det})
    atTop (𝓝 0)

private theorem TwoSLSSubsetRankFailureProbabilityConditions.instrumentFailure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ}
    (h : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X) :
    Tendsto
      (fun m => μ (
        {ω | ¬ IsUnit
          (((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω).det)} ∪
        {ω | ¬ IsUnit
          (((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω)
              (stackRegressors Zb m ω)).det)}))
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun m =>
        μ {ω | ¬ IsUnit
          (((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω).det)} +
        μ {ω | ¬ IsUnit
          (((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω)
              (stackRegressors Zb m ω)).det)}) atTop (𝓝 0) := by
    simpa only [zero_add] using h.maintained_instrument.add h.full_instrument
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hsum (Eventually.of_forall fun _ => zero_le _) ?_
  exact Eventually.of_forall fun m => measure_union_le _ _

private theorem tendstoInMeasure_sub_zero_of_measure_ne_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {X Y : ℕ → Ω → E}
    (hbad : Tendsto (fun m => μ {ω | X m ω ≠ Y m ω}) atTop (𝓝 0)) :
    TendstoInMeasure μ (Y - X) atTop (fun _ => 0) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
    (Eventually.of_forall fun _ => zero_le _) ?_
  exact Eventually.of_forall fun m => measure_mono (by
    intro ω hω
    simp only [Set.mem_setOf_eq, Pi.sub_apply] at hω ⊢
    intro hEq
    rw [hEq, sub_self, edist_self] at hω
    exact (not_le_of_gt hε) hω)

omit [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype l] [DecidableEq l] [Fintype la] [DecidableEq la]
  [Fintype lb] [DecidableEq lb] in
/-- Full-instrument homoskedasticity implies maintained-instrument
homoskedasticity for the left instrument block.

This is the sigma-algebra monotonicity step used by the Theorem 12.17
full-instrument homoskedastic facade: `Za₀` is a measurable projection of
`[Za₀,Zb₀]`, so a constant conditional second moment given the full instrument
vector remains constant after conditioning only on `Za₀`. -/
theorem HomoskedasticErrorVariance.of_twoSLSCombined_left
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Finite la] [Finite lb]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ} {e : ℕ → Ω → ℝ}
    (hZfull0 : Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e) :
    HomoskedasticErrorVariance μ Za e := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let leftProj : ((la ⊕ lb) → ℝ) → (la → ℝ) :=
    fun z a => z (Sum.inl a)
  have hleft_meas : Measurable leftProj := by
    exact (continuous_pi fun a => continuous_apply (Sum.inl a)).measurable
  have hfactor : Za 0 = leftProj ∘ Zfull 0 := by
    funext ω a
    rfl
  have hle : conditioningSpace (Za 0) ≤ conditioningSpace (Zfull 0) :=
    conditioningSpace_le_of_factor hleft_meas hfactor
  exact HomoskedasticErrorVariance.of_conditioningSpace_le
    (μ := μ) (X₁ := Za) (X₂ := Zfull) hle hZfull0 hhomoFull

omit [DecidableEq k] in
set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Homoskedastic full-instrument score covariance identity in Hansen's
combined-moment notation.

This is the reusable `QZZ`-target wrapper used by the overidentification tests:
the Chapter 7 homoskedastic score-covariance lemma gives
`scoreCovMat μ Z e = σ² popGram μ Z`, and the Chapter 12 combined-Gram bridge
identifies `popGram μ Z` with the instrument block of the `[Z,X]` population
Gram. -/
theorem scoreCovMat_eq_errorVariance_smul_twoSLSCombinedQZZ_of_assumption12_2_homoskedastic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e) :
    scoreCovMat μ Z e =
      errorVariance μ e •
        twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) := by
  let hIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e :=
    h.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Z X e :=
    hIid.toGramConditions
  have hpop :
      popGram μ Z =
        twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) :=
    popGram_eq_twoSLSCombinedQZZ_popGram
      (μ := μ) (Z := Z) (X := X)
      hGram.toTwoSLSGramInstrumentMomentRankConditions.instrument_moments.int_outer
      hGram.toTwoSLSGramInstrumentMomentRankConditions.combined_gram.int_outer
  have hcov_base :
      scoreCovMat μ Z e = errorVariance μ e • popGram μ Z :=
    scoreCovMat_eq_errorVariance_smul_popGram_homo
      (μ := μ) (X := Z) (e := e)
      hGram.score_clt.toSampleCLTAssumption72
      hIid.toSampleVarianceAssumption74 hZ0 hhomo
  rw [hcov_base, hpop]

set_option maxHeartbeats 800000 in
-- This proof expands the concrete covariance matrix into primitive matrix operations.
/-- Newey residualized subset-score covariance measurability from row
measurability. -/
theorem twoSLSSubsetNeweyCriterionCovHatStar_aestronglyMeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (m : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ := by
  let Rmat : Ω → Matrix (Fin m) lb ℝ := fun ω =>
    twoSLSSubsetResidualizedInstrumentsStar
      (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
  let Zmat : ℕ → Ω → (la ⊕ lb) → ℝ := fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let Xmat : Ω → Matrix (Fin m) k ℝ := fun ω => fun i => X i.val ω
  have hR : AEStronglyMeasurable Rmat μ :=
    twoSLSSubsetResidualizedInstrumentsStar_aestronglyMeasurable_of_rows
      (μ := μ) (Za := Za) (Zb := Zb) hZa hZb m
  have hRt : AEStronglyMeasurable (fun ω => (Rmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hR
  have hZ : ∀ i, AEStronglyMeasurable (Zmat i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zmat i) ?_
    intro j
    cases j with
    | inl a =>
        exact (measurable_pi_apply a).comp_aemeasurable (hZa i).aemeasurable
    | inr b =>
        exact (measurable_pi_apply b).comp_aemeasurable (hZb i).aemeasurable
  have hXmat : AEStronglyMeasurable Xmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) (X := X) hX
  have hXhat : AEStronglyMeasurable
      (fun ω =>
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω)) μ :=
    fittedRegressorsStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Zmat) (X := X) hZ hX
  have hXhatT : AEStronglyMeasurable
      (fun ω =>
        (fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXhat
  have hRR : AEStronglyMeasurable (fun ω => (Rmat ω)ᵀ * Rmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRt.prodMk hR)
  have hRX : AEStronglyMeasurable
      (fun ω => (Rmat ω)ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω)) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRt.prodMk hXhat)
  have hXX : AEStronglyMeasurable
      (fun ω =>
        (fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω)) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXhatT.prodMk hXhat)
  have hXXinv : AEStronglyMeasurable
      (fun ω =>
        ((fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hXX
  have hRX_inv : AEStronglyMeasurable
      (fun ω => (Rmat ω)ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω) *
        ((fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRX.prodMk hXXinv)
  have hRX_inv_Xt : AEStronglyMeasurable
      (fun ω => (Rmat ω)ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω) *
        ((fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))⁻¹ *
        (fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRX_inv.prodMk hXhatT)
  have hcorrection : AEStronglyMeasurable
      (fun ω => (Rmat ω)ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω) *
        ((fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))ᵀ *
        fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))⁻¹ *
        (fittedRegressorsStar
          (fun i : Fin m => Zmat i.val ω) (fun i : Fin m => X i.val ω))ᵀ *
        Rmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRX_inv_Xt.prodMk hR)
  have hmiddle : AEStronglyMeasurable
      (fun ω => twoSLSSubsetNeweyMiddleStar
        (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
        (fun i : Fin m => X i.val ω)) μ := by
    simpa [twoSLSSubsetNeweyMiddleStar, Rmat, Zmat, Xmat, Matrix.mul_assoc] using
      hRR.sub hcorrection
  have hsigma : AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin m => Zmat i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    twoSLSSigmaSqHatStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Zmat) (X := X) (Y := Y) hZ hX hY
  have hcov : AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin m => Zmat i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω) •
        ((Fintype.card (Fin m) : ℝ)⁻¹ •
          twoSLSSubsetNeweyMiddleStar
            (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
            (fun i : Fin m => X i.val ω))) μ :=
    hsigma.smul (hmiddle.const_smul ((Fintype.card (Fin m) : ℝ)⁻¹))
  simpa [twoSLSSubsetNeweyCriterionCovHatStar, Zmat, Matrix.mul_assoc] using hcov

set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- The proof assembles four matrix CMTs over rectangular products.
/-- Newey subset covariance consistency from its four primitive CMT inputs.

The finite-sample bridge is
`twoSLSSubsetNeweyMiddleStar_card_inv_smul_eq_scoreMap_overidResidualMaker_sampleQZZ`:
`V̂_N = σ̂² Â(M̂Q̂_ZZ)Â'`.  This theorem assembles the continuous-mapping
step from convergence of `σ̂²`, the residualized-score map `Â`, the full
overidentification residual-maker `M̂`, and the full-instrument Gram `Q̂_ZZ`.
-/
theorem
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_scoreMap_residualMaker_sampleQZZ_eventuallyAE
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {M Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {sigma2 : ℝ}
    (hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hM_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)) μ)
    (hM : TendstoInMeasure μ
      (fun m ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))
      atTop (fun _ => M))
    (hQ_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ)
    (hQ : TendstoInMeasure μ
      (fun m ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => Q))
    (hrank : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))) :
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2 • (A * (M * Q) * Aᵀ)) := by
  let sigmaHat : ℕ → Ω → ℝ := fun m ω =>
    twoSLSSigmaSqHatStar
      (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
      (stackRegressors X m ω) (stackOutcomes Y m ω)
  let Ahat : ℕ → Ω → Matrix lb (la ⊕ lb) ℝ := fun m ω =>
    twoSLSSubsetResidualizedScoreMapStar
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
  let Mhat : ℕ → Ω → Matrix (la ⊕ lb) (la ⊕ lb) ℝ := fun m ω =>
    twoSLSOveridResidualMaker
      (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
      (stackRegressors X m ω)
  let Qhat : ℕ → Ω → Matrix (la ⊕ lb) (la ⊕ lb) ℝ := fun m ω =>
    sampleQZZ
      (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
  have hsigma_meas' : ∀ m, AEStronglyMeasurable (sigmaHat m) μ := by
    intro m
    simpa [sigmaHat] using hsigma_meas m
  have hsigma' : TendstoInMeasure μ sigmaHat atTop (fun _ => sigma2) := by
    simpa [sigmaHat] using hsigma
  have hA_meas' : ∀ m, AEStronglyMeasurable (Ahat m) μ := by
    intro m
    simpa [Ahat] using hA_meas m
  have hA' : TendstoInMeasure μ Ahat atTop (fun _ => A) := by
    simpa [Ahat] using hA
  have hM_meas' : ∀ m, AEStronglyMeasurable (Mhat m) μ := by
    intro m
    simpa [Mhat] using hM_meas m
  have hM' : TendstoInMeasure μ Mhat atTop (fun _ => M) := by
    simpa [Mhat] using hM
  have hQ_meas' : ∀ m, AEStronglyMeasurable (Qhat m) μ := by
    intro m
    simpa [Qhat] using hQ_meas m
  have hQ' : TendstoInMeasure μ Qhat atTop (fun _ => Q) := by
    simpa [Qhat] using hQ
  have hMQ_meas : ∀ m,
      AEStronglyMeasurable (fun ω => Mhat m ω * Qhat m ω) μ := by
    intro m
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hM_meas' m).prodMk (hQ_meas' m))
  have hMQ : TendstoInMeasure μ (fun m ω => Mhat m ω * Qhat m ω)
      atTop (fun _ => M * Q) :=
    tendstoInMeasure_matrix_mul_rect hM_meas' hQ_meas' hM' hQ'
  have hAMQ_meas : ∀ m, AEStronglyMeasurable
      (fun ω => Ahat m ω * (Mhat m ω * Qhat m ω)) μ := by
    intro m
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hA_meas' m).prodMk (hMQ_meas m))
  have hAMQ : TendstoInMeasure μ
      (fun m ω => Ahat m ω * (Mhat m ω * Qhat m ω))
      atTop (fun _ => A * (M * Q)) :=
    tendstoInMeasure_matrix_mul_rect hA_meas' hMQ_meas hA' hMQ
  have hAt_meas : ∀ m, AEStronglyMeasurable (fun ω => (Ahat m ω)ᵀ) μ := by
    intro m
    exact (continuous_id.matrix_transpose).comp_aestronglyMeasurable (hA_meas' m)
  have hAt : TendstoInMeasure μ (fun m ω => (Ahat m ω)ᵀ)
      atTop (fun _ => Aᵀ) :=
    tendstoInMeasure_continuous_comp hA_meas' hA'
      (continuous_id.matrix_transpose)
  have hbody_meas : ∀ m, AEStronglyMeasurable
      (fun ω => Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ) μ := by
    intro m
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hAMQ_meas m).prodMk (hAt_meas m))
  have hbody : TendstoInMeasure μ
      (fun m ω => Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ)
      atTop (fun _ => A * (M * Q) * Aᵀ) :=
    tendstoInMeasure_matrix_mul_rect hAMQ_meas hAt_meas hAMQ hAt
  have hpair_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (sigmaHat m ω,
        Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ)) μ := by
    intro m
    exact (hsigma_meas' m).prodMk (hbody_meas m)
  have hpair : TendstoInMeasure μ
      (fun m ω => (sigmaHat m ω,
        Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ))
      atTop (fun _ => (sigma2, A * (M * Q) * Aᵀ)) :=
    tendstoInMeasure_prodMk hsigma' hbody
  have hraw : TendstoInMeasure μ
      (fun m ω =>
        sigmaHat m ω •
          (Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ))
      atTop (fun _ => sigma2 • (A * (M * Q) * Aᵀ)) := by
    have hcont : Continuous
        (fun p : ℝ × Matrix lb lb ℝ => p.1 • p.2) :=
      continuous_fst.smul continuous_snd
    exact tendstoInMeasure_continuous_comp hpair_meas hpair hcont
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hraw
  filter_upwards [eventually_gt_atTop 0, hrank] with m hm hrank_m
  filter_upwards [hrank_m] with ω hrank_ω
  · classical
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    rcases hrank_ω.1 with ⟨instZa⟩
    rcases hrank_ω.2 with ⟨instZ⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instZ
    have hmid :=
      twoSLSSubsetNeweyMiddleStar_card_inv_smul_eq_scoreMap_overidResidualMaker_sampleQZZ
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω)
    calc
      sigmaHat m ω •
          (Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ) =
          sigmaHat m ω •
            ((Fintype.card (Fin m) : ℝ)⁻¹ •
              twoSLSSubsetNeweyMiddleStar
                (stackRegressors Za m ω) (stackRegressors Zb m ω)
                (stackRegressors X m ω)) := by
            rw [hmid]
      _ =
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) := by
          rfl

set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- The proof assembles four rectangular matrix CMTs and a high-probability bridge.
/-- High-probability-rank version of Newey subset covariance consistency.

The continuous-mapping limit is unconditional.  Its exact identification with
the feasible Newey covariance is used off the two singular instrument-Gram
events, whose union has probability tending to zero. -/
theorem
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_scoreMap_residualMaker_sampleQZZ_rankProbability
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {M Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {sigma2 : ℝ}
    (hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hM_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)) μ)
    (hM : TendstoInMeasure μ
      (fun m ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))
      atTop (fun _ => M))
    (hQ_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ)
    (hQ : TendstoInMeasure μ
      (fun m ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => Q))
    (hrank : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X) :
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2 • (A * (M * Q) * Aᵀ)) := by
  let sigmaHat : ℕ → Ω → ℝ := fun m ω =>
    twoSLSSigmaSqHatStar
      (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
      (stackRegressors X m ω) (stackOutcomes Y m ω)
  let Ahat : ℕ → Ω → Matrix lb (la ⊕ lb) ℝ := fun m ω =>
    twoSLSSubsetResidualizedScoreMapStar
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
  let Mhat : ℕ → Ω → Matrix (la ⊕ lb) (la ⊕ lb) ℝ := fun m ω =>
    twoSLSOveridResidualMaker
      (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
      (stackRegressors X m ω)
  let Qhat : ℕ → Ω → Matrix (la ⊕ lb) (la ⊕ lb) ℝ := fun m ω =>
    sampleQZZ
      (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
  let ideal : ℕ → Ω → Matrix lb lb ℝ := fun m ω =>
    sigmaHat m ω • (Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ)
  let feasible : ℕ → Ω → Matrix lb lb ℝ := fun m ω =>
    twoSLSSubsetNeweyCriterionCovHatStar
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω)
  have hsigma_meas' : ∀ m, AEStronglyMeasurable (sigmaHat m) μ :=
    fun m => by simpa [sigmaHat] using hsigma_meas m
  have hsigma' : TendstoInMeasure μ sigmaHat atTop (fun _ => sigma2) := by
    simpa [sigmaHat] using hsigma
  have hA_meas' : ∀ m, AEStronglyMeasurable (Ahat m) μ :=
    fun m => by simpa [Ahat] using hA_meas m
  have hA' : TendstoInMeasure μ Ahat atTop (fun _ => A) := by
    simpa [Ahat] using hA
  have hM_meas' : ∀ m, AEStronglyMeasurable (Mhat m) μ :=
    fun m => by simpa [Mhat] using hM_meas m
  have hM' : TendstoInMeasure μ Mhat atTop (fun _ => M) := by
    simpa [Mhat] using hM
  have hQ_meas' : ∀ m, AEStronglyMeasurable (Qhat m) μ :=
    fun m => by simpa [Qhat] using hQ_meas m
  have hQ' : TendstoInMeasure μ Qhat atTop (fun _ => Q) := by
    simpa [Qhat] using hQ
  have hMQ_meas : ∀ m,
      AEStronglyMeasurable (fun ω => Mhat m ω * Qhat m ω) μ := fun m =>
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hM_meas' m).prodMk (hQ_meas' m))
  have hMQ : TendstoInMeasure μ (fun m ω => Mhat m ω * Qhat m ω)
      atTop (fun _ => M * Q) :=
    tendstoInMeasure_matrix_mul_rect hM_meas' hQ_meas' hM' hQ'
  have hAMQ_meas : ∀ m,
      AEStronglyMeasurable (fun ω => Ahat m ω * (Mhat m ω * Qhat m ω)) μ :=
    fun m =>
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        ((hA_meas' m).prodMk (hMQ_meas m))
  have hAMQ : TendstoInMeasure μ
      (fun m ω => Ahat m ω * (Mhat m ω * Qhat m ω))
      atTop (fun _ => A * (M * Q)) :=
    tendstoInMeasure_matrix_mul_rect hA_meas' hMQ_meas hA' hMQ
  have hAt_meas : ∀ m, AEStronglyMeasurable (fun ω => (Ahat m ω)ᵀ) μ :=
    fun m => (continuous_id.matrix_transpose).comp_aestronglyMeasurable (hA_meas' m)
  have hAt : TendstoInMeasure μ (fun m ω => (Ahat m ω)ᵀ)
      atTop (fun _ => Aᵀ) :=
    tendstoInMeasure_continuous_comp hA_meas' hA' (continuous_id.matrix_transpose)
  have hbody_meas : ∀ m, AEStronglyMeasurable
      (fun ω => Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ) μ := fun m =>
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hAMQ_meas m).prodMk (hAt_meas m))
  have hbody : TendstoInMeasure μ
      (fun m ω => Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ)
      atTop (fun _ => A * (M * Q) * Aᵀ) :=
    tendstoInMeasure_matrix_mul_rect hAMQ_meas hAt_meas hAMQ hAt
  have hpair_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (sigmaHat m ω,
        Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ)) μ :=
    fun m => (hsigma_meas' m).prodMk (hbody_meas m)
  have hpair : TendstoInMeasure μ
      (fun m ω => (sigmaHat m ω,
        Ahat m ω * (Mhat m ω * Qhat m ω) * (Ahat m ω)ᵀ))
      atTop (fun _ => (sigma2, A * (M * Q) * Aᵀ)) :=
    tendstoInMeasure_prodMk hsigma' hbody
  have hideal : TendstoInMeasure μ ideal
      atTop (fun _ => sigma2 • (A * (M * Q) * Aᵀ)) := by
    have hcont : Continuous (fun p : ℝ × Matrix lb lb ℝ => p.1 • p.2) :=
      continuous_fst.smul continuous_snd
    simpa [ideal] using tendstoInMeasure_continuous_comp hpair_meas hpair hcont
  have hne : Tendsto (fun m => μ {ω | ideal m ω ≠ feasible m ω})
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hrank.instrumentFailure (Eventually.of_forall fun _ => zero_le _) ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    refine measure_mono ?_
    intro ω hneq
    by_contra hbad
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hbad
    classical
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) :=
      Matrix.invertibleOfIsUnitDet
        (A := (stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) hbad.1
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
      Matrix.invertibleOfIsUnitDet
        (A := (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) hbad.2
    apply hneq
    dsimp [ideal, feasible, sigmaHat, Ahat, Mhat, Qhat]
    have hmid :=
      twoSLSSubsetNeweyMiddleStar_card_inv_smul_eq_scoreMap_overidResidualMaker_sampleQZZ
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω)
    rw [← hmid]
    rfl
  simpa [feasible] using
    tendstoInMeasure_congr_of_measure_ne_tendsto_zero hideal hne

set_option linter.style.longLine false in
/-- Pointwise-rank compatibility wrapper for
`twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_scoreMap_residualMaker_sampleQZZ_eventuallyAE`. -/
theorem
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_scoreMap_residualMaker_sampleQZZ
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {M Q : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {sigma2 : ℝ}
    (hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hM_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)) μ)
    (hM : TendstoInMeasure μ
      (fun m ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))
      atTop (fun _ => M))
    (hQ_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ)
    (hQ : TendstoInMeasure μ
      (fun m ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => Q))
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))) :
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2 • (A * (M * Q) * Aᵀ)) :=
  twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_scoreMap_residualMaker_sampleQZZ_eventuallyAE
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
    (A := A) (M := M) (Q := Q) (sigma2 := sigma2)
    hsigma_meas hsigma hA_meas hA hM_meas hM hQ_meas hQ
    (Eventually.of_forall fun m => ae_of_all μ fun ω => ⟨hZa m ω, hZ m ω⟩)

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- This wrapper unfolds the full-instrument sample-moment package through the
-- generic Newey covariance CMT above.
/-- Newey subset covariance consistency from Hansen's full-instrument
sample-moment package.

This supplies the residual-maker and `Q_ZZ` convergence inputs in
`twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_scoreMap_residualMaker_sampleQZZ`
from `TwoSLSSampleMomentConvergenceConditions`.  The remaining stochastic
inputs are scalar residual-variance consistency and convergence of the
residualized-score map. -/
theorem
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_eventuallyAE
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k (la ⊕ lb) ℝ}
    {QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QZX : Matrix (la ⊕ lb) k ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {sigma2 : ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e QXZ QZZ QZX)
    (hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hrank : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))) :
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => sigma2 •
          (A * (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX * QZZ) * Aᵀ)) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hM_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)) μ := by
    intro m
    simpa [Zfull, stackRegressors, Matrix.fromCols] using
      twoSLSOveridResidualMaker_aestronglyMeasurable_of_sample_moments
        (μ := μ) (Z := Zfull) (X := X) (e := e)
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) hMom m
  have hM : TendstoInMeasure μ
      (fun m ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))
      atTop (fun _ => twoSLSOveridPopulationResidualMaker QXZ QZZ QZX) := by
    simpa [Zfull, stackRegressors, Matrix.fromCols,
      twoSLSOveridPopulationResidualMaker] using
      twoSLSOveridResidualMaker_tendstoInMeasure_of_sample_moments
        (μ := μ) (Z := Zfull) (X := X) (e := e)
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) hMom
  have hQ_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ := by
    intro m
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hMom.qzz_meas m
  have hQ : TendstoInMeasure μ
      (fun m ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => QZZ) := by
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hMom.qzz_tendsto
  simpa [Zfull] using
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_scoreMap_residualMaker_sampleQZZ_eventuallyAE
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (A := A) (M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX)
      (Q := QZZ) (sigma2 := sigma2)
      hsigma_meas hsigma hA_meas hA hM_meas hM hQ_meas hQ hrank

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in
-- This wrapper unfolds the full sample-moment package through the matrix CMT.
/-- High-probability-rank companion to
`twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_eventuallyAE`. -/
theorem
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_rankProbability
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k (la ⊕ lb) ℝ}
    {QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QZX : Matrix (la ⊕ lb) k ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {sigma2 : ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e QXZ QZZ QZX)
    (hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hrank : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X) :
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => sigma2 •
          (A * (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX * QZZ) * Aᵀ)) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hM_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)) μ := by
    intro m
    simpa [Zfull, stackRegressors, Matrix.fromCols] using
      twoSLSOveridResidualMaker_aestronglyMeasurable_of_sample_moments
        (μ := μ) (Z := Zfull) (X := X) (e := e)
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) hMom m
  have hM : TendstoInMeasure μ
      (fun m ω =>
        twoSLSOveridResidualMaker
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))
      atTop (fun _ => twoSLSOveridPopulationResidualMaker QXZ QZZ QZX) := by
    simpa [Zfull, stackRegressors, Matrix.fromCols,
      twoSLSOveridPopulationResidualMaker] using
      twoSLSOveridResidualMaker_tendstoInMeasure_of_sample_moments
        (μ := μ) (Z := Zfull) (X := X) (e := e)
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) hMom
  have hQ_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ := by
    intro m
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hMom.qzz_meas m
  have hQ : TendstoInMeasure μ
      (fun m ω =>
        sampleQZZ
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => QZZ) := by
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hMom.qzz_tendsto
  simpa [Zfull] using
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_scoreMap_residualMaker_sampleQZZ_rankProbability
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (A := A) (M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX)
      (Q := QZZ) (sigma2 := sigma2)
      hsigma_meas hsigma hA_meas hA hM_meas hM hQ_meas hQ hrank

set_option linter.style.longLine false in
/-- Pointwise-rank compatibility wrapper for
`twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_eventuallyAE`. -/
theorem
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k (la ⊕ lb) ℝ}
    {QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QZX : Matrix (la ⊕ lb) k ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {sigma2 : ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e QXZ QZZ QZX)
    (hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))) :
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => sigma2 •
          (A * (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX * QZZ) * Aᵀ)) :=
  twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_eventuallyAE
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (A := A) (sigma2 := sigma2)
    hMom hsigma_meas hsigma hA_meas hA
    (Eventually.of_forall fun m => ae_of_all μ fun ω => ⟨hZa m ω, hZ m ω⟩)

set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- This wrapper combines the Newey CMT with the homoskedastic population
-- covariance identification for the canonical combined-population Q blocks.
/-- Newey subset covariance consistency to Hansen's displayed residualized
covariance target.

This is the covariance-target form needed by Hansen Theorem 12.17 wrappers:
sample moments give `M̂` and `Q̂_ZZ`, scalar residual-variance consistency gives
`σ̂²`, and `scoreCovMat = σ² Q_ZZ` identifies the CMT limit with the displayed
`twoSLSSubsetResidualizedScoreCovariance`. -/
theorem
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_covarianceTarget_eventuallyAE
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {sigma2 : ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e
      (twoSLSCombinedQXZ
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
      (twoSLSCombinedQZZ
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
      (twoSLSCombinedQZX
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))))
    (hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hrank : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hQXZ :
      twoSLSCombinedQXZ
          (popGram μ (twoSLSCombinedRegressors
            (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)) =
        (twoSLSCombinedQZX
          (popGram μ (twoSLSCombinedRegressors
            (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))ᵀ)
    (hQZZ_pos :
      (twoSLSCombinedQZZ
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))).PosDef)
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        sigma2 •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))) :
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) := by
  have hraw :=
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_eventuallyAE
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) (sigma2 := sigma2) hMom hsigma_meas hsigma hA_meas hA hrank
  have htarget :
      twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A =
        sigma2 •
          (A *
            (twoSLSOveridPopulationResidualMaker
              (twoSLSCombinedQXZ
                (popGram μ (twoSLSCombinedRegressors
                  (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
              (twoSLSCombinedQZZ
                (popGram μ (twoSLSCombinedRegressors
                  (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
              (twoSLSCombinedQZX
                (popGram μ (twoSLSCombinedRegressors
                  (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))) *
                twoSLSCombinedQZZ
                  (popGram μ (twoSLSCombinedRegressors
                    (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))) * Aᵀ) :=
    twoSLSSubsetResidualizedScoreCovariance_eq_sigma_scoreMap_residualMaker_popGram
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e)
      (A := A) (sigma2 := sigma2)
      hQXZ hQZZ_pos hMom.bread_nonsing hcov
  simpa [htarget] using hraw

set_option linter.style.longLine false in
/-- Pointwise-rank compatibility wrapper for
`twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_covarianceTarget_eventuallyAE`. -/
theorem
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_covarianceTarget
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {sigma2 : ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e
      (twoSLSCombinedQXZ
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
      (twoSLSCombinedQZZ
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
      (twoSLSCombinedQZX
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))))
    (hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hQXZ :
      twoSLSCombinedQXZ
          (popGram μ (twoSLSCombinedRegressors
            (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)) =
        (twoSLSCombinedQZX
          (popGram μ (twoSLSCombinedRegressors
            (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))ᵀ)
    (hQZZ_pos :
      (twoSLSCombinedQZZ
        (popGram μ (twoSLSCombinedRegressors
          (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))).PosDef)
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        sigma2 •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X))) :
    TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) :=
  twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_covarianceTarget_eventuallyAE
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) (sigma2 := sigma2) hMom hsigma_meas hsigma hA_meas hA
    (Eventually.of_forall fun m => ae_of_all μ fun ω => ⟨hZa m ω, hZ m ω⟩)
    hQXZ hQZZ_pos hcov

/-- Matrix kernel in Newey's subset-overidentification statistic,
`R (R'R - R'Xhat (Xhat'Xhat)^{-1} Xhat'R)^{-1} R'`. -/
noncomputable def twoSLSSubsetNeweyKernelStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ) :
    Matrix n n ℝ :=
  let Z := Matrix.fromCols Za Zb
  let Xhat := fittedRegressorsStar Z X
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let middle := Rᵀ * R - Rᵀ * Xhat * (Xhatᵀ * Xhat)⁻¹ * Xhatᵀ * R
  R * middle⁻¹ * Rᵀ

/-- Woodbury form of Newey's subset-overidentification kernel.

This is the deterministic kernel-correction identity below Hansen Theorem 12.17:
after identifying the maintained-instrument bread as the Schur complement of
the full fitted-regressor Gram with respect to `P_R`, Newey's kernel is
`P_R` plus the fitted-regressor correction
`P_R X̂ (X'P_aX)^{-1} X̂' P_R`. -/
theorem twoSLSSubsetNeweyKernelStar_eq_residualizedProjectionStar_add_fittedCorrection_of_schur
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ) (X : Matrix n k ℝ)
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    [Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
        fittedRegressorsStar (Matrix.fromCols Za Zb) X)]
    [Invertible (twoSLSMomentMatrixStar Za X)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb -
        (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X *
          ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
            fittedRegressorsStar (Matrix.fromCols Za Zb) X)⁻¹ *
          (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hschur : twoSLSMomentMatrixStar Za X =
      (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X -
        (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb *
          ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar Za Zb)⁻¹ *
          (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X) :
    twoSLSSubsetNeweyKernelStar Za Zb X =
      let Xhat := fittedRegressorsStar (Matrix.fromCols Za Zb) X
      let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
      PR + PR * Xhat * (twoSLSMomentMatrixStar Za X)⁻¹ * Xhatᵀ * PR := by
  let Z := Matrix.fromCols Za Zb
  let Xhat := fittedRegressorsStar Z X
  let R := twoSLSSubsetResidualizedInstrumentsStar Za Zb
  let G := Rᵀ * R
  let S := Xhatᵀ * Xhat
  let A := twoSLSMomentMatrixStar Za X
  let U := Rᵀ * Xhat
  let V := Xhatᵀ * R
  have hA : A = S - V * G⁻¹ * U := by
    simpa [A, S, V, G, U, Xhat, R, Z, Matrix.mul_assoc] using hschur
  have hmiddle_eq :
      G - U * S⁻¹ * V =
        Rᵀ * R - Rᵀ * Xhat * (Xhatᵀ * Xhat)⁻¹ * Xhatᵀ * R := by
    simp [G, U, S, V, Matrix.mul_assoc]
  letI : Invertible (G - U * S⁻¹ * V) := by
    rw [hmiddle_eq]
    infer_instance
  have hwood :
      (G - U * S⁻¹ * V)⁻¹ =
        G⁻¹ + G⁻¹ * U * A⁻¹ * V * G⁻¹ :=
    woodbury_sub_nonsingInv G U S A V hA
  dsimp [twoSLSSubsetNeweyKernelStar, twoSLSSubsetResidualizedProjectionStar]
  rw [← hmiddle_eq, hwood]
  simp [Z, R, Xhat, G, U, V, A, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Numerator of Newey's subset-overidentification statistic. -/
noncomputable def twoSLSSubsetNeweyNumeratorStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  let Z := Matrix.fromCols Za Zb
  let ehat := twoSLSResidualStar Z X Y
  ehat ⬝ᵥ (twoSLSSubsetNeweyKernelStar Za Zb X *ᵥ ehat)

/-- Newey's subset numerator as a quadratic form in the residualized excluded
instrument score. -/
theorem twoSLSSubsetNeweyNumeratorStar_eq_residualizedScoreQuadraticStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
      let g := twoSLSSubsetResidualizedScoreStar Za Zb X Y
      let middle := twoSLSSubsetNeweyMiddleStar Za Zb X
      g ⬝ᵥ (middle⁻¹ *ᵥ g) := by
  unfold twoSLSSubsetNeweyNumeratorStar twoSLSSubsetNeweyKernelStar
    twoSLSSubsetResidualizedScoreStar twoSLSSubsetNeweyMiddleStar
  simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.dotProduct_mulVec,
    vecMul_eq_mulVec_transpose]

/-- Newey's subset-overidentification statistic is the Chapter 9 criterion
statistic for the normalized residualized excluded-instrument score and
covariance `σ̂² n⁻¹(R'R - R'X̂(X̂'X̂)⁻¹X̂'R)`. -/
theorem twoSLSSubsetNeweyStatOrZero_eq_criterionJStatOrZero_residualizedScore
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSSubsetNeweyStatOrZero Za Zb X Y =
      criterionJStatOrZero
        ((Real.sqrt (Fintype.card n : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar Za Zb X Y)
        (twoSLSSubsetNeweyCriterionCovHatStar Za Zb X Y) := by
  let N : ℝ := Fintype.card n
  let rootInv : ℝ := (Real.sqrt N)⁻¹
  let Z := Matrix.fromCols Za Zb
  let g := twoSLSSubsetResidualizedScoreStar Za Zb X Y
  let middle := twoSLSSubsetNeweyMiddleStar Za Zb X
  let sigma := twoSLSSigmaSqHatStar Z X Y
  by_cases hn0 : Fintype.card n = 0
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn0
    simp [twoSLSSubsetNeweyStatOrZero, twoSLSSubsetResidualizedScoreStar,
      twoSLSSubsetNeweyCriterionCovHatStar, twoSLSSubsetNeweyMiddleStar,
      twoSLSSubsetResidualizedInstrumentsStar, twoSLSSigmaSqHatStar,
      sampleErrorSecondMoment, criterionJStatOrZero]
  haveI : Nonempty n :=
    Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  have hN_pos : 0 < N := by
    simpa [N] using
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card n) :
        0 < (Fintype.card n : ℝ))
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hcov_inv :
      (sigma • (N⁻¹ • middle))⁻¹ = (sigma⁻¹ * N) • middle⁻¹ := by
    rw [nonsingInv_smul, nonsingInv_smul]
    simp [smul_smul]
  have hroot_sq : rootInv * rootInv * N = 1 := by
    have hsqrt_ne : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN_pos)
    dsimp [rootInv]
    field_simp [hsqrt_ne, hN_ne]
    rw [Real.sq_sqrt hN_pos.le]
  have hscale : rootInv * (sigma⁻¹ * N * rootInv) = sigma⁻¹ := by
    calc
      rootInv * (sigma⁻¹ * N * rootInv)
          = sigma⁻¹ * (rootInv * rootInv * N) := by ring
      _ = sigma⁻¹ := by rw [hroot_sq, mul_one]
  have hcrit :
      criterionJStatOrZero (rootInv • g) (sigma • (N⁻¹ • middle)) =
        (g ⬝ᵥ (middle⁻¹ *ᵥ g)) / sigma := by
    rw [criterionJStatOrZero, hcov_inv]
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul]
    rw [dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    change rootInv * (sigma⁻¹ * N) * (rootInv *
        (g ⬝ᵥ (middle⁻¹ *ᵥ g))) =
      (g ⬝ᵥ (middle⁻¹ *ᵥ g)) / sigma
    rw [show rootInv * (sigma⁻¹ * N) * (rootInv *
        (g ⬝ᵥ (middle⁻¹ *ᵥ g))) =
        rootInv * (sigma⁻¹ * N * rootInv) *
          (g ⬝ᵥ (middle⁻¹ *ᵥ g)) by ring]
    rw [hscale]
    ring
  have hstat :
      twoSLSSubsetNeweyStatOrZero Za Zb X Y =
        (g ⬝ᵥ (middle⁻¹ *ᵥ g)) / sigma := by
    rw [twoSLSSubsetNeweyStatOrZero]
    have hnum :=
      twoSLSSubsetNeweyNumeratorStar_eq_residualizedScoreQuadraticStar
        Za Zb X Y
    simpa [twoSLSSubsetNeweyNumeratorStar, g, middle, sigma, Z] using
      congrArg (fun t => t / sigma) hnum
  calc
    twoSLSSubsetNeweyStatOrZero Za Zb X Y =
        (g ⬝ᵥ (middle⁻¹ *ᵥ g)) / sigma := hstat
    _ = criterionJStatOrZero (rootInv • g) (sigma • (N⁻¹ • middle)) := hcrit.symm
    _ = criterionJStatOrZero
        ((Real.sqrt (Fintype.card n : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar Za Zb X Y)
        (twoSLSSubsetNeweyCriterionCovHatStar Za Zb X Y) := by
      simp [twoSLSSubsetNeweyCriterionCovHatStar, Z, middle, sigma, N, rootInv, g]

/-- Numerator form of
`twoSLSSubsetNeweyKernelStar_eq_residualizedProjectionStar_add_fittedCorrection_of_schur`.

This exposes the exact scalar correction delivered by the Woodbury step before
using the full-model normal equations to match Hansen's restricted-residual
correction term. -/
theorem twoSLSSubsetNeweyNumeratorStar_eq_residualizedProjectionCorrectionQuadratic_of_schur
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    [Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
        fittedRegressorsStar (Matrix.fromCols Za Zb) X)]
    [Invertible (twoSLSMomentMatrixStar Za X)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb -
        (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X *
          ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
            fittedRegressorsStar (Matrix.fromCols Za Zb) X)⁻¹ *
          (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hschur : twoSLSMomentMatrixStar Za X =
      (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X -
        (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb *
          ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar Za Zb)⁻¹ *
          (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X) :
    twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
      let Z := Matrix.fromCols Za Zb
      let ehat := twoSLSResidualStar Z X Y
      let Xhat := fittedRegressorsStar Z X
      let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
      ehat ⬝ᵥ ((PR + PR * Xhat * (twoSLSMomentMatrixStar Za X)⁻¹ * Xhatᵀ * PR) *ᵥ ehat) := by
  rw [twoSLSSubsetNeweyNumeratorStar]
  rw [twoSLSSubsetNeweyKernelStar_eq_residualizedProjectionStar_add_fittedCorrection_of_schur
    Za Zb X hschur]

/-- Sargan-difference statistic `C = S - S_a`, computed with each model's own
residual-variance denominator. -/
noncomputable def twoSLSSubsetSarganDiffStatOrZero
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  twoSLSSarganStatOrZero (Matrix.fromCols Za Zb) X Y -
    twoSLSSarganStatOrZero Za X Y

/-- Ordinary subset Sargan-difference statistic measurability from row
measurability. -/
theorem twoSLSSubsetSarganDiffStatOrZero_aemeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (m : ℕ) :
    AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ := by
  let Z : ℕ → Ω → (la ⊕ lb) → ℝ := fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hZ : ∀ i, AEStronglyMeasurable (Z i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Z i) ?_
    intro j
    cases j with
    | inl a =>
        exact (measurable_pi_apply a).comp_aemeasurable (hZa i).aemeasurable
    | inr b =>
        exact (measurable_pi_apply b).comp_aemeasurable (hZb i).aemeasurable
  have hfull : AEMeasurable
      (fun ω =>
        twoSLSSarganStatOrZero
          (fun i : Fin m => Z i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    twoSLSSarganStatOrZero_aemeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hmaintained : AEMeasurable
      (fun ω =>
        twoSLSSarganStatOrZero
          (fun i : Fin m => Za i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    twoSLSSarganStatOrZero_aemeasurable_of_rows
      (μ := μ) (Z := Za) (X := X) (Y := Y) hZa hX hY
  simpa [twoSLSSubsetSarganDiffStatOrZero, Z] using hfull.sub hmaintained

/-- Common-denominator Sargan-difference statistic `C*`, using the full-model
`σ̂²` denominator for both quadratic numerators. -/
noncomputable def twoSLSSubsetSarganDiffCommonSigmaStatOrZero
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  let Z := Matrix.fromCols Za Zb
  (twoSLSSarganNumeratorStar Z X Y - twoSLSSarganNumeratorStar Za X Y) /
    twoSLSSigmaSqHatStar Z X Y

/-- Numerator of the common-denominator Sargan-difference statistic `C*`. -/
noncomputable def twoSLSSubsetSarganDiffCommonSigmaNumeratorStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  let Z := Matrix.fromCols Za Zb
  twoSLSSarganNumeratorStar Z X Y - twoSLSSarganNumeratorStar Za X Y

/-- Common-denominator subset Sargan-difference statistic measurability from
row measurability. -/
theorem twoSLSSubsetSarganDiffCommonSigmaStatOrZero_aemeasurable_of_rows
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (m : ℕ) :
    AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (fun i : Fin m => Za i.val ω) (fun i : Fin m => Zb i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ := by
  let Z : ℕ → Ω → (la ⊕ lb) → ℝ := fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hZ : ∀ i, AEStronglyMeasurable (Z i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Z i) ?_
    intro j
    cases j with
    | inl a =>
        exact (measurable_pi_apply a).comp_aemeasurable (hZa i).aemeasurable
    | inr b =>
        exact (measurable_pi_apply b).comp_aemeasurable (hZb i).aemeasurable
  have hfull_num : AEStronglyMeasurable
      (fun ω =>
        twoSLSSarganNumeratorStar
          (fun i : Fin m => Z i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    twoSLSSarganNumeratorStar_aestronglyMeasurable_of_rows
      (μ := μ) (m := m) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hmaintained_num : AEStronglyMeasurable
      (fun ω =>
        twoSLSSarganNumeratorStar
          (fun i : Fin m => Za i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    twoSLSSarganNumeratorStar_aestronglyMeasurable_of_rows
      (μ := μ) (m := m) (Z := Za) (X := X) (Y := Y) hZa hX hY
  have hsigma : AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin m => Z i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    twoSLSSigmaSqHatStar_aestronglyMeasurable_of_rows
      (μ := μ) (n := m) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hstat : AEMeasurable
      (fun ω =>
        (twoSLSSarganNumeratorStar
            (fun i : Fin m => Z i.val ω)
            (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω) -
          twoSLSSarganNumeratorStar
            (fun i : Fin m => Za i.val ω)
            (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) /
        twoSLSSigmaSqHatStar
          (fun i : Fin m => Z i.val ω)
          (fun i : Fin m => X i.val ω) (fun i : Fin m => Y i.val ω)) μ :=
    (hfull_num.sub hmaintained_num).aemeasurable.div hsigma.aemeasurable
  simpa [twoSLSSubsetSarganDiffCommonSigmaStatOrZero, Z, Matrix.fromCols] using
    hstat

/-- The restricted-instrument Sargan numerator evaluated at the full-model
residual.  This is one of the two finite-sample algebra obligations needed for
Hansen's raw `N = C*` identity. -/
noncomputable def twoSLSSubsetRestrictedSarganNumeratorAtFullResidualStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  let Z := Matrix.fromCols Za Zb
  let ehat := twoSLSResidualStar Z X Y
  ehat ⬝ᵥ (instrumentProjectionStar Za *ᵥ ehat)

omit [DecidableEq n] in
/-- Full-model 2SLS normal equation specialized to the subset-overidentification
instrument partition.  This is the finite-sample orthogonality used after the
Woodbury kernel correction to replace the residualized-instrument fitted score
by the maintained-instrument correction score. -/
theorem twoSLSSubsetFullResidual_fittedScore_eq_zero
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    (hunit : IsUnit (twoSLSMomentMatrixStar (Matrix.fromCols Za Zb) X).det) :
    (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *ᵥ
      twoSLSResidualStar (Matrix.fromCols Za Zb) X Y = 0 :=
  fittedRegressorsStar_transpose_mulVec_twoSLSResidualStar_of_nonsingular
    (Matrix.fromCols Za Zb) X Y hunit

omit [DecidableEq n] in
/-- Restricted-model 2SLS coefficient expressed around the full-model
coefficient.

For the full instrument set `Z = [Z_a,Z_b]` and full residual `ê`, this is the
finite-sample algebra
`β̂_a = β̂ + (X'P_aX)^{-1} X'P_a ê` on the nonsingular restricted-bread
branch.  It is the first deterministic step in Hansen's Theorem 12.17
restricted-residual calculation. -/
theorem twoSLSSubsetRestrictedBetaStar_eq_fullBetaStar_add_correction
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hunit : IsUnit (twoSLSMomentMatrixStar Za X).det) :
    twoSLSBetaStar Za X Y =
      twoSLSBetaStar (Matrix.fromCols Za Zb) X Y +
        (twoSLSMomentMatrixStar Za X)⁻¹ *ᵥ
          twoSLSMomentVectorStar Za X
            (twoSLSResidualStar (Matrix.fromCols Za Zb) X Y) := by
  let Z := Matrix.fromCols Za Zb
  let βfull := twoSLSBetaStar Z X Y
  let ehat := twoSLSResidualStar Z X Y
  have hY : X *ᵥ βfull + ehat = Y := by
    ext i
    simp [βfull, ehat, twoSLSResidualStar]
  have hlin :=
    twoSLSBetaStar_sub_identity_of_nonsingular
      Za X βfull ehat hunit
  rw [hY] at hlin
  ext j
  have hj := congrFun hlin j
  simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
  linarith

/-- Hansen's restricted residual formula in Theorem 12.17.

With `Z = [Z_a,Z_b]`, full residual `ê`, and `P_a` the maintained-instrument
projection, the restricted residual satisfies
`ẽ = (I - X (X'P_aX)^{-1} X'P_a) ê` on the nonsingular restricted-bread branch. -/
theorem twoSLSSubsetRestrictedResidualStar_eq_fullResidual_sub_correction
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hunit : IsUnit (twoSLSMomentMatrixStar Za X).det) :
    twoSLSResidualStar Za X Y =
      ((1 : Matrix n n ℝ) -
          X * (twoSLSMomentMatrixStar Za X)⁻¹ * Xᵀ *
            instrumentProjectionStar Za) *ᵥ
        twoSLSResidualStar (Matrix.fromCols Za Zb) X Y := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  unfold twoSLSResidualStar
  rw [twoSLSSubsetRestrictedBetaStar_eq_fullBetaStar_add_correction
    Za Zb X Y hunit]
  rw [Matrix.mulVec_add]
  ext i
  simp [twoSLSResidualStar, twoSLSMomentVectorStar, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]
  ring

/-- The restricted-instrument Sargan numerator rewritten through Hansen's
restricted-residual correction operator.

This is the numerator-level bridge that follows from the exact residual formula
`ẽ = (I - X (X'P_aX)^{-1} X'P_a) ê`.  It keeps the correction term visible
instead of replacing the restricted residual by the full residual. -/
theorem twoSLSSarganNumeratorStar_eq_restrictedResidualCorrectionQuadraticStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hunit : IsUnit (twoSLSMomentMatrixStar Za X).det) :
    twoSLSSarganNumeratorStar Za X Y =
      let ehat := twoSLSResidualStar (Matrix.fromCols Za Zb) X Y
      let H :=
        X * (twoSLSMomentMatrixStar Za X)⁻¹ * Xᵀ *
          instrumentProjectionStar Za
      let etilde := ((1 : Matrix n n ℝ) - H) *ᵥ ehat
      etilde ⬝ᵥ (instrumentProjectionStar Za *ᵥ etilde) := by
  rw [twoSLSSarganNumeratorStar,
    twoSLSSubsetRestrictedResidualStar_eq_fullResidual_sub_correction
      Za Zb X Y hunit]

/-- Common-denominator Sargan-difference numerator with the restricted
numerator expanded through the residual-correction operator.

This is the finite-sample numerator surface needed before the Woodbury step in
Hansen's `N = C*` proof: the remaining algebra must identify Newey's kernel
with the full projection-difference plus the visible restricted-bread
correction. -/
theorem twoSLSSubsetSarganDiffCommonSigmaNumeratorStar_eq_fullMinusRestrictedCorrectionQuadraticStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hunit : IsUnit (twoSLSMomentMatrixStar Za X).det) :
    twoSLSSubsetSarganDiffCommonSigmaNumeratorStar Za Zb X Y =
      twoSLSSarganNumeratorStar (Matrix.fromCols Za Zb) X Y -
        (let ehat := twoSLSResidualStar (Matrix.fromCols Za Zb) X Y
         let H :=
          X * (twoSLSMomentMatrixStar Za X)⁻¹ * Xᵀ *
            instrumentProjectionStar Za
         let etilde := ((1 : Matrix n n ℝ) - H) *ᵥ ehat
         etilde ⬝ᵥ (instrumentProjectionStar Za *ᵥ etilde)) := by
  rw [twoSLSSubsetSarganDiffCommonSigmaNumeratorStar]
  rw [twoSLSSarganNumeratorStar_eq_restrictedResidualCorrectionQuadraticStar
    Za Zb X Y hunit]

/-- Common-sigma numerator written using the projection difference
`P_[Za,Zb] - P_Za` and the full-model residual. -/
noncomputable def twoSLSSubsetSarganProjectionDiffNumeratorStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : ℝ :=
  let Z := Matrix.fromCols Za Zb
  let ehat := twoSLSResidualStar Z X Y
  ehat ⬝ᵥ ((instrumentProjectionStar Z - instrumentProjectionStar Za) *ᵥ ehat)

/-- Full-model normal equations identify Hansen's two correction scores in the
subset-overidentification proof.

With `Z = [Z_a,Z_b]`, `P_Z = P_a + P_R`, and full-model residual `ê`, the
normal equation `Xhat'ê = 0` gives
`X'P_a ê = -Xhat'P_R ê`.  This is the finite-sample bridge used in Hansen
Theorem 12.17 to match Newey's Woodbury correction with the restricted-residual
correction. -/
theorem twoSLSSubsetFullResidual_restrictedScore_eq_neg_residualizedFittedScore
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hunit : IsUnit (twoSLSMomentMatrixStar (Matrix.fromCols Za Zb) X).det) :
    twoSLSMomentVectorStar Za X
        (twoSLSResidualStar (Matrix.fromCols Za Zb) X Y) =
      -((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *ᵥ
        (twoSLSSubsetResidualizedProjectionStar Za Zb *ᵥ
          twoSLSResidualStar (Matrix.fromCols Za Zb) X Y)) := by
  let Z := Matrix.fromCols Za Zb
  let ehat := twoSLSResidualStar Z X Y
  let Xhat := fittedRegressorsStar Z X
  let Pa := instrumentProjectionStar Za
  let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
  have hprojection : instrumentProjectionStar Z = Pa + PR := by
    simpa [Z, Pa, PR] using
      instrumentProjectionStar_fromCols_eq_sum_residualizedProjectionStar Za Zb
  have hXhat : Xhat = (Pa + PR) * X := by
    dsimp [Xhat, fittedRegressorsStar, Z, Pa, PR]
    rw [hprojection]
  have hPaT : Paᵀ = Pa := by
    simpa [Pa] using instrumentProjectionStar_transpose_of_nonsingular Za
  have hPRT : PRᵀ = PR := by
    simpa [PR] using twoSLSSubsetResidualizedProjectionStar_transpose Za Zb
  have hPaPR : Pa * PR = 0 := by
    simpa [Pa, PR] using
      instrumentProjectionStar_mul_twoSLSSubsetResidualizedProjectionStar Za Zb
  have hPRidem : PR * PR = PR := by
    simpa [PR] using twoSLSSubsetResidualizedProjectionStar_idempotent Za Zb
  have hnormal : Xhatᵀ *ᵥ ehat = 0 := by
    simpa [Z, Xhat, ehat] using
      fittedRegressorsStar_transpose_mulVec_twoSLSResidualStar_of_nonsingular
        Z X Y hunit
  have hXhatPR :
      Xhatᵀ *ᵥ (PR *ᵥ ehat) = (Xᵀ * PR) *ᵥ ehat := by
    calc
      Xhatᵀ *ᵥ (PR *ᵥ ehat) =
          ((Pa + PR) * X)ᵀ *ᵥ (PR *ᵥ ehat) := by rw [hXhat]
      _ = (Xᵀ * (Pa + PR)) *ᵥ (PR *ᵥ ehat) := by
            rw [Matrix.transpose_mul, Matrix.transpose_add, hPaT, hPRT]
      _ = (Xᵀ * ((Pa + PR) * PR)) *ᵥ ehat := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (Xᵀ * PR) *ᵥ ehat := by
            rw [Matrix.add_mul, hPaPR, hPRidem]
            simp
  have hsplit :
      Xhatᵀ *ᵥ ehat =
        twoSLSMomentVectorStar Za X ehat + Xhatᵀ *ᵥ (PR *ᵥ ehat) := by
    calc
      Xhatᵀ *ᵥ ehat =
          ((Pa + PR) * X)ᵀ *ᵥ ehat := by rw [hXhat]
      _ = (Xᵀ * (Pa + PR)) *ᵥ ehat := by
            rw [Matrix.transpose_mul, Matrix.transpose_add, hPaT, hPRT]
      _ = ((Xᵀ * Pa) + (Xᵀ * PR)) *ᵥ ehat := by
            rw [Matrix.mul_add]
      _ = (Xᵀ * Pa) *ᵥ ehat + (Xᵀ * PR) *ᵥ ehat := by
            rw [Matrix.add_mulVec]
      _ = twoSLSMomentVectorStar Za X ehat + Xhatᵀ *ᵥ (PR *ᵥ ehat) := by
            rw [hXhatPR]
            simp [twoSLSMomentVectorStar, Pa]
  have hsum :
      twoSLSMomentVectorStar Za X ehat +
          Xhatᵀ *ᵥ (PR *ᵥ ehat) = 0 := by
    simpa [hsplit] using hnormal
  ext j
  have hj := congrFun hsum j
  simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hj ⊢
  linarith

/-- The restricted residual correction has the usual weighted-projection
quadratic form.

This is the deterministic algebra behind Hansen's display after substituting
the restricted residual formula in Theorem 12.17:
`ẽ'P_aẽ = ê'P_aê - ê'P_aX(X'P_aX)^{-1}X'P_aê`. -/
theorem twoSLSSarganRestrictedCorrectionQuadratic_eq_fullResidual_sub_maintainedCorrection
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible (twoSLSMomentMatrixStar Za X)] :
    (let ehat := twoSLSResidualStar (Matrix.fromCols Za Zb) X Y
     let A := twoSLSMomentMatrixStar Za X
     let Pa := instrumentProjectionStar Za
     let H := X * A⁻¹ * Xᵀ * Pa
     let etilde := ((1 : Matrix n n ℝ) - H) *ᵥ ehat
     etilde ⬝ᵥ (Pa *ᵥ etilde)) =
      (let ehat := twoSLSResidualStar (Matrix.fromCols Za Zb) X Y
       let A := twoSLSMomentMatrixStar Za X
       let Pa := instrumentProjectionStar Za
       ehat ⬝ᵥ (Pa *ᵥ ehat) -
        ehat ⬝ᵥ ((Pa * X * A⁻¹ * Xᵀ * Pa) *ᵥ ehat)) := by
  let ehat := twoSLSResidualStar (Matrix.fromCols Za Zb) X Y
  let A := twoSLSMomentMatrixStar Za X
  let Pa := instrumentProjectionStar Za
  let H := X * A⁻¹ * Xᵀ * Pa
  let C := Pa * X * A⁻¹ * Xᵀ * Pa
  have hPaT : Paᵀ = Pa := by
    simpa [Pa] using instrumentProjectionStar_transpose_of_nonsingular Za
  have hPaIdem : Pa * Pa = Pa := by
    simpa [Pa] using instrumentProjectionStar_idempotent_of_nonsingular Za
  have hA : A = Xᵀ * Pa * X := by
    rfl
  have hAT : Aᵀ = A := by
    rw [hA]
    simp [Matrix.transpose_mul, hPaT, Matrix.mul_assoc]
  have hAinvT : (A⁻¹)ᵀ = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAT]
  have hHT : Hᵀ = Pa * X * A⁻¹ * Xᵀ := by
    simp [H, Matrix.transpose_mul, hPaT, hAinvT, Matrix.mul_assoc]
  have hPaH : Pa * H = C := by
    simp [H, C, Matrix.mul_assoc]
  have hHTPa : Hᵀ * Pa = C := by
    simp [hHT, C, Matrix.mul_assoc]
  have hHTPaH : Hᵀ * Pa * H = C := by
    calc
      Hᵀ * Pa * H = (Hᵀ * Pa) * H := by
            rw [Matrix.mul_assoc]
      _ = C * H := by
            rw [hHTPa]
      _ = (Pa * X * A⁻¹ * Xᵀ * Pa) * (X * A⁻¹ * Xᵀ * Pa) := by
            rfl
      _ = Pa * X * (A⁻¹ * (Xᵀ * Pa * X)) * A⁻¹ * Xᵀ * Pa := by
            simp [Matrix.mul_assoc]
      _ = Pa * X * (A⁻¹ * A) * A⁻¹ * Xᵀ * Pa := by
            rw [← hA]
      _ = C := by
            rw [← invOf_eq_nonsing_inv A, invOf_mul_self]
            simp [C, Matrix.mul_assoc]
  have hmatrix :
      ((1 : Matrix n n ℝ) - H)ᵀ * Pa * ((1 : Matrix n n ℝ) - H) =
        Pa - C := by
    calc
      ((1 : Matrix n n ℝ) - H)ᵀ * Pa * ((1 : Matrix n n ℝ) - H)
          = (1 - Hᵀ) * Pa * (1 - H) := by
              rw [Matrix.transpose_sub, Matrix.transpose_one]
      _ = Pa - Hᵀ * Pa - (Pa * H - Hᵀ * (Pa * H)) := by
              simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      _ = Pa - C := by
              have hHTPaH' : Hᵀ * (Pa * H) = C := by
                rw [← Matrix.mul_assoc, hHTPaH]
              have hHTC : Hᵀ * C = C := by
                calc
                  Hᵀ * C = Hᵀ * (Pa * H) := by rw [hPaH]
                  _ = C := hHTPaH'
              rw [hPaH, hHTPa, hHTC]
              abel
  have hquad :=
    quadraticForm_mulVec_eq_pullback_rect
      (B := ((1 : Matrix n n ℝ) - H)) (A := Pa) (x := ehat)
  calc
    (let etilde := ((1 : Matrix n n ℝ) - H) *ᵥ ehat
     etilde ⬝ᵥ (Pa *ᵥ etilde)) =
        ehat ⬝ᵥ ((((1 : Matrix n n ℝ) - H)ᵀ * Pa *
          ((1 : Matrix n n ℝ) - H)) *ᵥ ehat) := hquad
    _ = ehat ⬝ᵥ ((Pa - C) *ᵥ ehat) := by rw [hmatrix]
    _ = ehat ⬝ᵥ (Pa *ᵥ ehat) -
        ehat ⬝ᵥ (C *ᵥ ehat) := by
          simp [Matrix.sub_mulVec, dotProduct_sub]

/-- Full-model normal equations make Newey's Woodbury correction and the
restricted-residual correction the same scalar quadratic. -/
theorem twoSLSSubsetFittedCorrectionQuadratic_eq_maintainedCorrectionQuadratic
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hunit : IsUnit (twoSLSMomentMatrixStar (Matrix.fromCols Za Zb) X).det) :
    (let ehat := twoSLSResidualStar (Matrix.fromCols Za Zb) X Y
     let Xhat := fittedRegressorsStar (Matrix.fromCols Za Zb) X
     let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
     let A := twoSLSMomentMatrixStar Za X
     ehat ⬝ᵥ ((PR * Xhat * A⁻¹ * Xhatᵀ * PR) *ᵥ ehat)) =
      (let ehat := twoSLSResidualStar (Matrix.fromCols Za Zb) X Y
       let Pa := instrumentProjectionStar Za
       let A := twoSLSMomentMatrixStar Za X
       ehat ⬝ᵥ ((Pa * X * A⁻¹ * Xᵀ * Pa) *ᵥ ehat)) := by
  let ehat := twoSLSResidualStar (Matrix.fromCols Za Zb) X Y
  let Xhat := fittedRegressorsStar (Matrix.fromCols Za Zb) X
  let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
  let Pa := instrumentProjectionStar Za
  let A := twoSLSMomentMatrixStar Za X
  have hscore :
      twoSLSMomentVectorStar Za X ehat =
        -(Xhatᵀ *ᵥ (PR *ᵥ ehat)) := by
    simpa [ehat, Xhat, PR] using
      twoSLSSubsetFullResidual_restrictedScore_eq_neg_residualizedFittedScore
        Za Zb X Y hunit
  have hPRT : PRᵀ = PR := by
    simpa [PR] using twoSLSSubsetResidualizedProjectionStar_transpose Za Zb
  have hPaT : Paᵀ = Pa := by
    simpa [Pa] using instrumentProjectionStar_transpose_of_nonsingular Za
  have hleft :
      ehat ⬝ᵥ ((PR * Xhat * A⁻¹ * Xhatᵀ * PR) *ᵥ ehat) =
        (Xhatᵀ *ᵥ (PR *ᵥ ehat)) ⬝ᵥ
          (A⁻¹ *ᵥ (Xhatᵀ *ᵥ (PR *ᵥ ehat))) := by
    have hB : (PR * Xhat)ᵀ = Xhatᵀ * PR := by
      rw [Matrix.transpose_mul, hPRT]
    have h :=
      (quadraticForm_mulVec_eq_pullback_rect
        (B := (PR * Xhat)ᵀ) (A := A⁻¹) (x := ehat)).symm
    calc
      ehat ⬝ᵥ ((PR * Xhat * A⁻¹ * Xhatᵀ * PR) *ᵥ ehat) =
          ehat ⬝ᵥ ((((PR * Xhat)ᵀ)ᵀ * A⁻¹ * (PR * Xhat)ᵀ) *ᵥ ehat) := by
            rw [hB]
            simp [Matrix.transpose_mul, hPRT, Matrix.mul_assoc]
      _ = (Xhatᵀ *ᵥ (PR *ᵥ ehat)) ⬝ᵥ
          (A⁻¹ *ᵥ (Xhatᵀ *ᵥ (PR *ᵥ ehat))) := by
            rw [h]
            rw [hB]
            simp [Matrix.mulVec_mulVec]
  have hright :
      ehat ⬝ᵥ ((Pa * X * A⁻¹ * Xᵀ * Pa) *ᵥ ehat) =
        twoSLSMomentVectorStar Za X ehat ⬝ᵥ
          (A⁻¹ *ᵥ twoSLSMomentVectorStar Za X ehat) := by
    have hB : (Pa * X)ᵀ = Xᵀ * Pa := by
      rw [Matrix.transpose_mul, hPaT]
    have hscorePa : (Pa * X)ᵀ *ᵥ ehat =
        twoSLSMomentVectorStar Za X ehat := by
      rw [hB]
      simp [twoSLSMomentVectorStar, Pa]
    have h :=
      (quadraticForm_mulVec_eq_pullback_rect
        (B := (Pa * X)ᵀ) (A := A⁻¹) (x := ehat)).symm
    calc
      ehat ⬝ᵥ ((Pa * X * A⁻¹ * Xᵀ * Pa) *ᵥ ehat) =
          ehat ⬝ᵥ ((((Pa * X)ᵀ)ᵀ * A⁻¹ * (Pa * X)ᵀ) *ᵥ ehat) := by
            rw [hB]
            simp [Matrix.transpose_mul, hPaT, Matrix.mul_assoc]
      _ = ((Pa * X)ᵀ *ᵥ ehat) ⬝ᵥ
          (A⁻¹ *ᵥ ((Pa * X)ᵀ *ᵥ ehat)) := h
      _ = twoSLSMomentVectorStar Za X ehat ⬝ᵥ
          (A⁻¹ *ᵥ twoSLSMomentVectorStar Za X ehat) := by
            rw [hscorePa]
  rw [hleft, hright, hscore]
  simp [Matrix.mulVec_neg]

/-- Newey's Woodbury numerator equals Hansen's common-denominator
Sargan-difference numerator once the Schur-complement identity and the
full-model normal equations are supplied by the finite-sample nonsingularity
assumptions.

This is the direct deterministic `N = C*` numerator bridge in Hansen Theorem
12.17; it does not assume the final statistic equality, and it replaces the
older restricted-numerator shortcut with the explicit fitted-correction versus
restricted-correction identity. -/
theorem twoSLSSubsetNeweyNumeratorStar_eq_commonSigmaNumeratorStar_of_normalEquations
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    [Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
        fittedRegressorsStar (Matrix.fromCols Za Zb) X)]
    [Invertible (twoSLSMomentMatrixStar Za X)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb -
        (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X *
          ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
            fittedRegressorsStar (Matrix.fromCols Za Zb) X)⁻¹ *
          (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hunit : IsUnit (twoSLSMomentMatrixStar (Matrix.fromCols Za Zb) X).det) :
    twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaNumeratorStar Za Zb X Y := by
  let Z := Matrix.fromCols Za Zb
  let ehat := twoSLSResidualStar Z X Y
  let Xhat := fittedRegressorsStar Z X
  let Pa := instrumentProjectionStar Za
  let PR := twoSLSSubsetResidualizedProjectionStar Za Zb
  let A := twoSLSMomentMatrixStar Za X
  let F := PR * Xhat * A⁻¹ * Xhatᵀ * PR
  let C := Pa * X * A⁻¹ * Xᵀ * Pa
  have hprojection : instrumentProjectionStar Z = Pa + PR := by
    simpa [Z, Pa, PR] using
      instrumentProjectionStar_fromCols_eq_sum_residualizedProjectionStar Za Zb
  have hnewey :
      twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
        ehat ⬝ᵥ ((PR + F) *ᵥ ehat) := by
    have hschur := twoSLSSubsetSchurComplement_eq_restrictedMomentMatrix
      Za Zb X
    simpa [Z, ehat, Xhat, PR, A, F] using
      twoSLSSubsetNeweyNumeratorStar_eq_residualizedProjectionCorrectionQuadratic_of_schur
        Za Zb X Y hschur
  have hneweyExpanded :
      twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
        ehat ⬝ᵥ (PR *ᵥ ehat) + ehat ⬝ᵥ (F *ᵥ ehat) := by
    rw [hnewey]
    simp [Matrix.add_mulVec, dotProduct_add]
  have hcorr :
      ehat ⬝ᵥ (F *ᵥ ehat) = ehat ⬝ᵥ (C *ᵥ ehat) := by
    simpa [Z, ehat, Xhat, PR, Pa, A, F, C] using
      twoSLSSubsetFittedCorrectionQuadratic_eq_maintainedCorrectionQuadratic
        Za Zb X Y hunit
  have hrestricted :
      (let ehat := twoSLSResidualStar Z X Y
       let A := twoSLSMomentMatrixStar Za X
       let Pa := instrumentProjectionStar Za
       let H := X * A⁻¹ * Xᵀ * Pa
       let etilde := ((1 : Matrix n n ℝ) - H) *ᵥ ehat
       etilde ⬝ᵥ (Pa *ᵥ etilde)) =
        ehat ⬝ᵥ (Pa *ᵥ ehat) - ehat ⬝ᵥ (C *ᵥ ehat) := by
    simpa [Z, ehat, A, Pa, C] using
      twoSLSSarganRestrictedCorrectionQuadratic_eq_fullResidual_sub_maintainedCorrection
        Za Zb X Y
  have hfullNum :
      twoSLSSarganNumeratorStar (Matrix.fromCols Za Zb) X Y =
        ehat ⬝ᵥ ((Pa + PR) *ᵥ ehat) := by
    change ehat ⬝ᵥ (instrumentProjectionStar Z *ᵥ ehat) =
      ehat ⬝ᵥ ((Pa + PR) *ᵥ ehat)
    rw [hprojection]
  have hcommonExpanded :
      twoSLSSubsetSarganDiffCommonSigmaNumeratorStar Za Zb X Y =
        ehat ⬝ᵥ (PR *ᵥ ehat) + ehat ⬝ᵥ (C *ᵥ ehat) := by
    rw [
      twoSLSSubsetSarganDiffCommonSigmaNumeratorStar_eq_fullMinusRestrictedCorrectionQuadraticStar
        Za Zb X Y (Matrix.isUnit_det_of_invertible (twoSLSMomentMatrixStar Za X))]
    rw [hrestricted, hfullNum]
    rw [Matrix.add_mulVec, dotProduct_add]
    ring
  rw [hneweyExpanded, hcommonExpanded, hcorr]

/-- Newey's statistic is its exposed numerator divided by the full-model
residual variance. -/
theorem twoSLSSubsetNeweyStatOrZero_eq_neweyNumeratorStar_div
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSSubsetNeweyStatOrZero Za Zb X Y =
      twoSLSSubsetNeweyNumeratorStar Za Zb X Y /
        twoSLSSigmaSqHatStar (Matrix.fromCols Za Zb) X Y := by
  simp [twoSLSSubsetNeweyStatOrZero, twoSLSSubsetNeweyNumeratorStar,
    twoSLSSubsetNeweyKernelStar]

omit [DecidableEq n] in
/-- The common-denominator statistic is its exposed numerator divided by the
full-model residual variance. -/
theorem twoSLSSubsetSarganDiffCommonSigmaStatOrZero_eq_commonSigmaNumeratorStar_div
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaNumeratorStar Za Zb X Y /
        twoSLSSigmaSqHatStar (Matrix.fromCols Za Zb) X Y := by
  simp [twoSLSSubsetSarganDiffCommonSigmaStatOrZero,
    twoSLSSubsetSarganDiffCommonSigmaNumeratorStar]

omit [DecidableEq n] in
/-- Exact finite-sample decomposition of Hansen's common-denominator gap
`C* - C`.

The only source of discrepancy between the common-denominator Sargan-difference
statistic and the ordinary Sargan-difference statistic is the maintained-model
Sargan numerator multiplied by the difference of reciprocal residual-variance
estimators.  This is the algebraic core of the `C* - C = o_p(1)` step in
Hansen Theorem 12.17. -/
theorem twoSLSSubsetCommonSigmaMinusSarganDiff_eq_maintainedNumerator_mul_sigmaInvDiff
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) :
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero Za Zb X Y -
      twoSLSSubsetSarganDiffStatOrZero Za Zb X Y =
    ((twoSLSSigmaSqHatStar Za X Y)⁻¹ -
        (twoSLSSigmaSqHatStar (Matrix.fromCols Za Zb) X Y)⁻¹) *
      twoSLSSarganNumeratorStar Za X Y := by
  dsimp [twoSLSSubsetSarganDiffCommonSigmaStatOrZero,
    twoSLSSubsetSarganDiffCommonSigmaNumeratorStar,
    twoSLSSubsetSarganDiffStatOrZero, twoSLSSarganStatOrZero]
  ring

/-- Slutsky bridge for Hansen Theorem 12.17's `C* - C = o_p(1)` step.

It is enough to prove that the maintained-model Sargan numerator is
`O_p(1)` and that the reciprocal residual-variance estimators for the
maintained and full models differ by `o_p(1)`. -/
theorem twoSLSSubsetCommonSigmaMinusSarganDiff_tendsto_zero_of_maintainedNum_bounded_sigmaInvDiff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hnum : BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)))
    (hsigmaInvDiff : TendstoInMeasure μ
      (fun m ω =>
        (twoSLSSigmaSqHatStar
            (stackRegressors Za m ω) (stackRegressors X m ω)
            (stackOutcomes Y m ω))⁻¹ -
          (twoSLSSigmaSqHatStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω))⁻¹)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) := by
  have hprod :=
    TendstoInMeasure.mul_boundedInProbability
      (μ := μ)
      (X := fun m ω =>
        (twoSLSSigmaSqHatStar
            (stackRegressors Za m ω) (stackRegressors X m ω)
            (stackOutcomes Y m ω))⁻¹ -
          (twoSLSSigmaSqHatStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω))⁻¹)
      (Y := fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω))
      hsigmaInvDiff hnum
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hprod
  intro m
  exact ae_of_all μ (fun ω => by
    simpa using
      (twoSLSSubsetCommonSigmaMinusSarganDiff_eq_maintainedNumerator_mul_sigmaInvDiff
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)).symm)

/-- Variant of
`twoSLSSubsetCommonSigmaMinusSarganDiff_tendsto_zero_of_maintainedNum_bounded_sigmaInvDiff`
where the reciprocal variance estimators are each shown to converge to the
same scalar limit. -/
theorem twoSLSSubsetCommonSigmaMinusSarganDiff_tendsto_zero_of_maintainedNum_bounded_sigmaInv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ} {sigmaInv : ℝ}
    (hnum : BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)))
    (hmaintainedInv : TendstoInMeasure μ
      (fun m ω =>
        (twoSLSSigmaSqHatStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω))⁻¹)
      atTop (fun _ => sigmaInv))
    (hfullInv : TendstoInMeasure μ
      (fun m ω =>
        (twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))⁻¹)
      atTop (fun _ => sigmaInv)) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) := by
  have hmaintained0 := TendstoInMeasure.sub_limit_zero_real hmaintainedInv
  have hfull0 := TendstoInMeasure.sub_limit_zero_real hfullInv
  have hdiff0 :
      TendstoInMeasure μ
        (fun m ω =>
          ((twoSLSSigmaSqHatStar
              (stackRegressors Za m ω) (stackRegressors X m ω)
              (stackOutcomes Y m ω))⁻¹ - sigmaInv) -
            ((twoSLSSigmaSqHatStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) (stackOutcomes Y m ω))⁻¹ - sigmaInv))
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_zero_real hmaintained0 hfull0
  have hsigmaInvDiff : TendstoInMeasure μ
      (fun m ω =>
        (twoSLSSigmaSqHatStar
            (stackRegressors Za m ω) (stackRegressors X m ω)
            (stackOutcomes Y m ω))⁻¹ -
          (twoSLSSigmaSqHatStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω))⁻¹)
      atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hdiff0
    intro m
    exact ae_of_all μ (fun ω => by ring)
  exact
    twoSLSSubsetCommonSigmaMinusSarganDiff_tendsto_zero_of_maintainedNum_bounded_sigmaInvDiff
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      hnum hsigmaInvDiff

/-- Kernel equality reduces Newey's numerator to the projection-difference
numerator. -/
theorem twoSLSSubsetNeweyNumeratorStar_eq_projectionDiffNumeratorStar_of_kernel_eq
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hkernel : twoSLSSubsetNeweyKernelStar Za Zb X =
      instrumentProjectionStar (Matrix.fromCols Za Zb) - instrumentProjectionStar Za) :
    twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
      twoSLSSubsetSarganProjectionDiffNumeratorStar Za Zb X Y := by
  simp [twoSLSSubsetNeweyNumeratorStar,
    twoSLSSubsetSarganProjectionDiffNumeratorStar, hkernel]

omit [DecidableEq n] in
/-- Rewriting the restricted Sargan numerator with the full residual reduces the
projection-difference numerator to the common-sigma Sargan-difference
numerator. -/
theorem twoSLSSubsetSarganProjectionDiffNumeratorStar_eq_commonSigmaNumeratorStar
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hrestricted : twoSLSSarganNumeratorStar Za X Y =
      twoSLSSubsetRestrictedSarganNumeratorAtFullResidualStar Za Zb X Y) :
    twoSLSSubsetSarganProjectionDiffNumeratorStar Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaNumeratorStar Za Zb X Y := by
  have hrestricted_eval :
      (let Z := Matrix.fromCols Za Zb
       let ehat := twoSLSResidualStar Z X Y
       ehat ⬝ᵥ (instrumentProjectionStar Za *ᵥ ehat)) =
        twoSLSSarganNumeratorStar Za X Y := by
    simpa [twoSLSSubsetRestrictedSarganNumeratorAtFullResidualStar] using
      hrestricted.symm
  simp [twoSLSSubsetSarganProjectionDiffNumeratorStar,
    twoSLSSubsetSarganDiffCommonSigmaNumeratorStar,
    twoSLSSarganNumeratorStar, hrestricted_eval, Matrix.sub_mulVec,
    dotProduct_sub]

/-- Numerator-level `N = C*` reduction from the two finite-sample algebra
obligations: the Newey kernel is the projection difference, and the restricted
Sargan numerator may be evaluated using the full-model residual. -/
theorem twoSLSSubsetNeweyNumeratorStar_eq_commonSigmaNumeratorStar_of_kernel_eq
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hkernel : twoSLSSubsetNeweyKernelStar Za Zb X =
      instrumentProjectionStar (Matrix.fromCols Za Zb) - instrumentProjectionStar Za)
    (hrestricted : twoSLSSarganNumeratorStar Za X Y =
      twoSLSSubsetRestrictedSarganNumeratorAtFullResidualStar Za Zb X Y) :
    twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaNumeratorStar Za Zb X Y := by
  calc
    twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
        twoSLSSubsetSarganProjectionDiffNumeratorStar Za Zb X Y :=
      twoSLSSubsetNeweyNumeratorStar_eq_projectionDiffNumeratorStar_of_kernel_eq
        Za Zb X Y hkernel
    _ = twoSLSSubsetSarganDiffCommonSigmaNumeratorStar Za Zb X Y :=
      twoSLSSubsetSarganProjectionDiffNumeratorStar_eq_commonSigmaNumeratorStar
        Za Zb X Y hrestricted

/-- Statistic-level `N = C*` from the numerator equality.  This uses only the
shared common denominator, not the final statistic equality as an assumption. -/
theorem twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_numerator_eq
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hnum : twoSLSSubsetNeweyNumeratorStar Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaNumeratorStar Za Zb X Y) :
    twoSLSSubsetNeweyStatOrZero Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero Za Zb X Y := by
  simp [twoSLSSubsetNeweyStatOrZero_eq_neweyNumeratorStar_div,
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero_eq_commonSigmaNumeratorStar_div,
    hnum]

/-- Direct finite-sample statistic-level `N = C*` bridge for Hansen Theorem
12.17.

This wrapper combines the projection-decomposition/Schur-complement algebra
with the full-model 2SLS normal equations, so callers can cite the exact
statistic identity without separately composing the numerator bridge. -/
theorem twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_normalEquations
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    [Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
        fittedRegressorsStar (Matrix.fromCols Za Zb) X)]
    [Invertible (twoSLSMomentMatrixStar Za X)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb -
        (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X *
          ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
            fittedRegressorsStar (Matrix.fromCols Za Zb) X)⁻¹ *
          (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hunit : IsUnit (twoSLSMomentMatrixStar (Matrix.fromCols Za Zb) X).det) :
    twoSLSSubsetNeweyStatOrZero Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero Za Zb X Y :=
  twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_numerator_eq Za Zb X Y
    (twoSLSSubsetNeweyNumeratorStar_eq_commonSigmaNumeratorStar_of_normalEquations
      Za Zb X Y hunit)

/-- Under the finite-sample normal equations used in Hansen Theorem 12.17,
the common-denominator statistic `C*` is the same concrete Chapter 9 criterion
statistic as Newey's residualized-score statistic. -/
theorem twoSLSSubsetSarganDiffCommonSigmaStatOrZero_eq_criterionJStatOrZero_residualizedScore
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    [Invertible (Zaᵀ * Za)]
    [Invertible ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    [Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
        fittedRegressorsStar (Matrix.fromCols Za Zb) X)]
    [Invertible (twoSLSMomentMatrixStar Za X)]
    [Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb -
        (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X *
          ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
            fittedRegressorsStar (Matrix.fromCols Za Zb) X)⁻¹ *
          (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb)]
    (hunit : IsUnit (twoSLSMomentMatrixStar (Matrix.fromCols Za Zb) X).det) :
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero Za Zb X Y =
      criterionJStatOrZero
        ((Real.sqrt (Fintype.card n : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar Za Zb X Y)
        (twoSLSSubsetNeweyCriterionCovHatStar Za Zb X Y) := by
  rw [← twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_normalEquations
    (Za := Za) (Zb := Zb) (X := X) (Y := Y) hunit]
  exact twoSLSSubsetNeweyStatOrZero_eq_criterionJStatOrZero_residualizedScore
    Za Zb X Y

/-- Deterministic algebra package for Hansen's raw finite-sample `N = C*`
identity.  Its fields are the two smaller matrix/residual equalities needed by
`twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat`; it deliberately does not
assume the final statistic equality. -/
structure TwoSLSSubsetFiniteSampleAlgebra
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ) : Prop where
  newey_kernel_eq_projectionDiff : twoSLSSubsetNeweyKernelStar Za Zb X =
    instrumentProjectionStar (Matrix.fromCols Za Zb) - instrumentProjectionStar Za
  restricted_sargan_numerator_eq_full_residual :
    twoSLSSarganNumeratorStar Za X Y =
      twoSLSSubsetRestrictedSarganNumeratorAtFullResidualStar Za Zb X Y

/-- The finite-sample algebra package gives the raw statistic identity
`N = C*`. -/
theorem TwoSLSSubsetFiniteSampleAlgebra.neweyStat_eq_commonSigmaStat
    {Za : Matrix n la ℝ} {Zb : Matrix n lb ℝ}
    {X : Matrix n k ℝ} {Y : n → ℝ}
    (h : TwoSLSSubsetFiniteSampleAlgebra Za Zb X Y) :
    twoSLSSubsetNeweyStatOrZero Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero Za Zb X Y :=
  twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_numerator_eq Za Zb X Y
    (twoSLSSubsetNeweyNumeratorStar_eq_commonSigmaNumeratorStar_of_kernel_eq
      Za Zb X Y h.newey_kernel_eq_projectionDiff
      h.restricted_sargan_numerator_eq_full_residual)

section Asymptotics

variable {Ω Ωlim : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
variable {μ : Measure Ω} {ν : Measure Ωlim}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private theorem tendstoInDistribution_congr_eventuallyAE
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    {X Y : ℕ → Ω → E} {Z : Ωlim → E}
    (hXY : ∀ᶠ m in atTop, X m =ᵐ[μ] Y m)
    (hY : ∀ m, AEMeasurable (Y m) μ)
    (h : TendstoInDistribution X atTop Z (fun _ => μ) ν) :
    TendstoInDistribution Y atTop Z (fun _ => μ) ν := by
  refine ⟨hY, h.aemeasurable_limit, ?_⟩
  have hmap : (fun m =>
        (⟨Measure.map (X m) μ,
          Measure.isProbabilityMeasure_map (h.forall_aemeasurable m)⟩ :
          ProbabilityMeasure E)) =ᶠ[atTop]
      (fun m =>
        (⟨Measure.map (Y m) μ,
          Measure.isProbabilityMeasure_map (hY m)⟩ : ProbabilityMeasure E)) := by
    filter_upwards [hXY] with m hm
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (X m) μ = Measure.map (Y m) μ
    exact Measure.map_congr hm
  simpa using (tendsto_congr' hmap).mp h.tendsto

omit [MeasurableSpace Ω] in
set_option linter.style.longLine false in
/-- Pointwise stacked-sample version of
`twoSLSSubsetDualSchurComplement_invertible_of_normalEquations`.

It converts the finite-sample normal-equation branch assumptions used by the
Theorem 12.17 routes into the dual Newey Schur branch.  The maintained moment
branch is not used by itself; the residualized-instrument Gram and full
fitted-regressor Gram branches are part of the bridge. -/
theorem twoSLSSubsetDualSchurComplement_invertible_of_stackedNormalEquations
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ}
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω)))) :
    ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))) := by
  intro m ω
  classical
  rcases hZa m ω with ⟨instZa⟩
  rcases hZ m ω with ⟨instZ⟩
  rcases hR m ω with ⟨instR⟩
  rcases hFitted m ω with ⟨instFitted⟩
  rcases hMaintainedMoment m ω with ⟨instMaintained⟩
  letI : Invertible
      ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
  letI : Invertible
      ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
        Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instZ
  letI : Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instR
  letI : Invertible
      ((fittedRegressorsStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))ᵀ *
        fittedRegressorsStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)) := instFitted
  letI : Invertible
      (twoSLSMomentMatrixStar
        (stackRegressors Za m ω) (stackRegressors X m ω)) := instMaintained
  exact
    twoSLSSubsetDualSchurComplement_invertible_of_normalEquations
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω)

private theorem isUnit_det_smul_of_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ} {A : Matrix ι ι ℝ} (hc : c ≠ 0) (hA : IsUnit A.det) :
    IsUnit (c • A).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hA.ne_zero

private theorem tendstoInMeasure_inv_const_real
    {X : ℕ → Ω → ℝ} {c : ℝ}
    (hX_meas : ∀ n, AEStronglyMeasurable (X n) μ)
    (hX : TendstoInMeasure μ X atTop (fun _ => c))
    (hc : c ≠ 0) :
    TendstoInMeasure μ (fun n ω => (X n ω)⁻¹) atTop (fun _ => c⁻¹) := by
  have hInv_meas : ∀ n, AEStronglyMeasurable (fun ω => (X n ω)⁻¹) μ := by
    intro n
    exact
      (measurable_inv.comp_aemeasurable
        (hX_meas n).aemeasurable).aestronglyMeasurable
  exact tendstoInMeasure_continuousAt_const_comp hX_meas hInv_meas hX
    (continuousAt_inv₀ hc)

private theorem matrixMulVec_tendstoInDistribution_of_vector_and_rect_matrix
    {p q : Type*} [Fintype p] [Fintype q]
    {T : ℕ → Ω → q → ℝ} {Zlim : Ωlim → q → ℝ}
    {Ahat : ℕ → Ω → Matrix p q ℝ} {A : Matrix p q ℝ}
    (hT : TendstoInDistribution T atTop Zlim (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A)) :
    TendstoInDistribution
      (fun n ω => Ahat n ω *ᵥ T n ω)
      atTop (fun ω => A *ᵥ Zlim ω) (fun _ => μ) ν := by
  letI : BorelSpace (Matrix p q ℝ) := ⟨rfl⟩
  have hA_meas' : ∀ n, AEMeasurable (Ahat n) μ :=
    fun n => (hA_meas n).aemeasurable
  have hcont : Continuous (fun x : (q → ℝ) × Matrix p q ℝ => x.2 *ᵥ x.1) :=
    Continuous.matrix_mulVec continuous_snd continuous_fst
  have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun x : (q → ℝ) × Matrix p q ℝ => x.2 *ᵥ x.1)
    hcont hA hA_meas'
  simpa [Function.comp_def] using hraw

private theorem tendstoInDistribution_of_limit_map_eq
    {E Ωtarget : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace Ωtarget]
    {η : Measure Ωtarget} [IsProbabilityMeasure η]
    {T : ℕ → Ω → E} {Z : Ωlim → E} {Y : Ωtarget → E}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hY : AEMeasurable Y η)
    (hmap : ν.map Z = η.map Y) :
    TendstoInDistribution T atTop Y (fun _ => μ) η := by
  refine ⟨hT.forall_aemeasurable, hY, ?_⟩
  have htarget :
      (⟨ν.map Z, Measure.isProbabilityMeasure_map hT.aemeasurable_limit⟩ :
          ProbabilityMeasure E) =
        ⟨η.map Y, Measure.isProbabilityMeasure_map hY⟩ := by
    exact Subtype.ext hmap
  simpa [htarget] using hT.tendsto

set_option linter.style.longLine false in
/-- Subset residualized-score CLT from a full-instrument residual-score CLT
and convergence of the explicit residualized-score map.

This is the stochastic counterpart of
`twoSLSSubsetResidualizedScoreStar_eq_scoreMap_mul_sarganResidualScoreStar`:
the residualized excluded-instrument score is obtained by applying a random
rectangular map to the full Sargan residual score. -/
theorem
    twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_fullResidualScoreMap_eventuallyAE
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {G : Ωlim → (la ⊕ lb) → ℝ}
    (hrank : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hTarget_meas : ∀ m : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hFullScore : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun ω => A *ᵥ G ω) (fun _ => μ) ν := by
  have hmap :=
    matrixMulVec_tendstoInDistribution_of_vector_and_rect_matrix
      (μ := μ) (ν := ν)
      (T := fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Zlim := G)
      (Ahat := fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      (A := A)
      hFullScore hA_meas hA
  apply tendstoInDistribution_congr_eventuallyAE (hY := hTarget_meas) (h := hmap)
  filter_upwards [hrank] with m hm
  filter_upwards [hm] with ω hω
  · classical
    rcases hω.1 with ⟨instZa⟩
    rcases hω.2 with ⟨instZ⟩
    letI : Invertible ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) :=
      instZa
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
      instZ
    change
      twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω) *ᵥ
        ((Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω)) =
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)
    rw [twoSLSSubsetResidualizedScoreStar_eq_scoreMap_mul_sarganResidualScoreStar]
    simp [Matrix.mulVec_smul]

set_option linter.style.longLine false in
/-- High-probability-rank version of the subset residualized-score Slutsky
bridge.

The exact score-map identity is used on the two nonsingular instrument-Gram
branches.  The complement need only have probability tending to zero. -/
theorem
    twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_fullResidualScoreMap_rankProbability
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {G : Ωlim → (la ⊕ lb) → ℝ}
    (hrank : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X)
    (hTarget_meas : ∀ m : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hFullScore : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun ω => A *ᵥ G ω) (fun _ => μ) ν := by
  let mapped : ℕ → Ω → lb → ℝ := fun m ω =>
    twoSLSSubsetResidualizedScoreMapStar
        (stackRegressors Za m ω) (stackRegressors Zb m ω) *ᵥ
      ((Real.sqrt (m : ℝ))⁻¹ •
        twoSLSSarganResidualScoreStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
  let target : ℕ → Ω → lb → ℝ := fun m ω =>
    (Real.sqrt (m : ℝ))⁻¹ •
      twoSLSSubsetResidualizedScoreStar
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)
  have hmap : TendstoInDistribution mapped atTop
      (fun ω => A *ᵥ G ω) (fun _ => μ) ν := by
    simpa [mapped] using
      matrixMulVec_tendstoInDistribution_of_vector_and_rect_matrix
        (μ := μ) (ν := ν)
        (T := fun (m : ℕ) (ω : Ω) =>
          (Real.sqrt (m : ℝ))⁻¹ •
            twoSLSSarganResidualScoreStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) (stackOutcomes Y m ω))
        (Zlim := G)
        (Ahat := fun m ω =>
          twoSLSSubsetResidualizedScoreMapStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (A := A) hFullScore hA_meas hA
  have hne : Tendsto (fun m => μ {ω | mapped m ω ≠ target m ω})
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hrank.instrumentFailure (Eventually.of_forall fun _ => zero_le _) ?_
    exact Eventually.of_forall fun m => measure_mono (by
      intro ω hneq
      by_contra hbad
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hbad
      classical
      letI : Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) :=
        Matrix.invertibleOfIsUnitDet
          (A := (stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) hbad.1
      letI : Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
        Matrix.invertibleOfIsUnitDet
          (A := (Matrix.fromCols (stackRegressors Za m ω)
              (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          hbad.2
      apply hneq
      dsimp [mapped, target]
      rw [twoSLSSubsetResidualizedScoreStar_eq_scoreMap_mul_sarganResidualScoreStar]
      simp [Matrix.mulVec_smul])
  have hdiff : TendstoInMeasure μ (target - mapped) atTop (fun _ => 0) :=
    tendstoInMeasure_sub_zero_of_measure_ne_tendsto_zero hne
  simpa [target] using
    tendstoInDistribution_of_tendstoInMeasure_sub
      (X := mapped) (Y := target) (Z := fun ω => A *ᵥ G ω)
      hmap hdiff (fun m => by simpa [target] using hTarget_meas m)

set_option linter.style.longLine false in
/-- Pointwise-rank compatibility wrapper for
`twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_fullResidualScoreMap_eventuallyAE`. -/
theorem twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_fullResidualScoreMap
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {G : Ωlim → (la ⊕ lb) → ℝ}
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hFullScore : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun ω => A *ᵥ G ω) (fun _ => μ) ν := by
  have hmap :=
    matrixMulVec_tendstoInDistribution_of_vector_and_rect_matrix
      (μ := μ) (ν := ν)
      (T := fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Zlim := G)
      (Ahat := fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      (A := A) hFullScore hA_meas hA
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hmap
  intro m
  exact ae_of_all μ fun ω => by
    classical
    rcases hZa m ω with ⟨instZa⟩
    rcases hZ m ω with ⟨instZ⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instZ
    change
      twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω) *ᵥ
        ((Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω) (stackOutcomes Y m ω)) =
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)
    rw [twoSLSSubsetResidualizedScoreStar_eq_scoreMap_mul_sarganResidualScoreStar]
    simp [Matrix.mulVec_smul]

/-- Proof-facing package for Hansen Theorem 12.17's denominator-substitution
step `C* - C = o_p(1)`.

The maintained-model Sargan numerator is required only through a genuine
distributional limit, which gives `O_p(1)` by the Chapter 6 tightness bridge.
The reciprocal variance equality is derived from consistency of the maintained
and full residual-variance estimators to the same nonzero `σ²`, rather than
assumed directly. -/
structure TwoSLSSubsetCommonSigmaDiffConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (sigma2 : ℝ) (Gnum : Ωlim → ℝ) : Prop where
  maintained_numerator_limit : TendstoInDistribution
    (fun m ω =>
      twoSLSSarganNumeratorStar
        (stackRegressors Za m ω) (stackRegressors X m ω)
        (stackOutcomes Y m ω))
    atTop Gnum (fun _ => μ) ν
  maintained_sigma_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      twoSLSSigmaSqHatStar
        (stackRegressors Za m ω) (stackRegressors X m ω)
        (stackOutcomes Y m ω)) μ
  maintained_sigma_tendsto : TendstoInMeasure μ
    (fun m ω =>
      twoSLSSigmaSqHatStar
        (stackRegressors Za m ω) (stackRegressors X m ω)
        (stackOutcomes Y m ω))
    atTop (fun _ => sigma2)
  full_sigma_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      twoSLSSigmaSqHatStar
        (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (stackRegressors X m ω) (stackOutcomes Y m ω)) μ
  full_sigma_tendsto : TendstoInMeasure μ
    (fun m ω =>
      twoSLSSigmaSqHatStar
        (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun _ => sigma2)
  sigma_ne : sigma2 ≠ 0

/-- The denominator-substitution package supplies the exact Slutsky input
`C* - C = o_p(1)` for Hansen Theorem 12.17. -/
theorem TwoSLSSubsetCommonSigmaDiffConditions.tendstoInMeasure_zero
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {sigma2 : ℝ} {Gnum : Ωlim → ℝ}
    (h : TwoSLSSubsetCommonSigmaDiffConditions μ ν Za Zb X Y sigma2 Gnum) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) := by
  have hnum : BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)) :=
    BoundedInProbability.of_tendstoInDistribution h.maintained_numerator_limit
  have hmaintainedInv : TendstoInMeasure μ
      (fun m ω =>
        (twoSLSSigmaSqHatStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω))⁻¹)
      atTop (fun _ => sigma2⁻¹) :=
    tendstoInMeasure_inv_const_real h.maintained_sigma_meas
      h.maintained_sigma_tendsto h.sigma_ne
  have hfullInv : TendstoInMeasure μ
      (fun m ω =>
        (twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))⁻¹)
      atTop (fun _ => sigma2⁻¹) :=
    tendstoInMeasure_inv_const_real h.full_sigma_meas
      h.full_sigma_tendsto h.sigma_ne
  exact
    twoSLSSubsetCommonSigmaMinusSarganDiff_tendsto_zero_of_maintainedNum_bounded_sigmaInv
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (sigmaInv := sigma2⁻¹) hnum hmaintainedInv hfullInv

namespace TwoSLSSubsetCommonSigmaDiffConditions

/-- Build Hansen Theorem 12.17's denominator-substitution package from the
maintained and full residual-variance consistency packages used in Theorem 12.3.

The only probabilistic input not supplied by the covariance-moment packages is
the maintained-model Sargan numerator limit, which is used solely for
tightness in the Slutsky denominator replacement. -/
theorem of_covarianceMomentConsistency
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZa : Matrix k la ℝ} {QZZa Omegaa : Matrix la la ℝ}
    {QZXa : Matrix la k ℝ}
    {QXZfull : Matrix k (la ⊕ lb) ℝ}
    {QZZfull Omegafull : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QZXfull : Matrix (la ⊕ lb) k ℝ}
    {sigma2 : ℝ} {Gnum : Ωlim → ℝ}
    (hnum : TendstoInDistribution
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω))
      atTop Gnum (fun _ => μ) ν)
    (hMaintained : TwoSLSCovarianceMomentConsistencyConditions
      μ Za X e Y QXZa QZZa Omegaa QZXa sigma2)
    (hFull : TwoSLSCovarianceMomentConsistencyConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y
        QXZfull QZZfull Omegafull QZXfull sigma2)
    (hsigma_ne : sigma2 ≠ 0) :
    TwoSLSSubsetCommonSigmaDiffConditions μ ν Za Zb X Y sigma2 Gnum where
  maintained_numerator_limit := hnum
  maintained_sigma_meas := hMaintained.sigma_meas
  maintained_sigma_tendsto := hMaintained.sigma_tendsto
  full_sigma_meas := by
    intro m
    simpa [stackRegressors, Matrix.fromCols] using hFull.sigma_meas m
  full_sigma_tendsto := by
    simpa [stackRegressors, Matrix.fromCols] using hFull.sigma_tendsto
  sigma_ne := hsigma_ne

/-- Build the denominator-substitution package from primitive mixed-moment
Assumption 12.2 packages for the maintained instrument set `Z_a` and the full
partitioned instrument set `[Z_a,Z_b]`.

This reuses the Chapter 12.3 residual-substitution constructors to derive both
residual-variance consistencies.  It does not assume the final subset
overidentification statistic limit. -/
theorem of_assumption12_2_joint_iid_mixed_moments
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {Gnum : Ωlim → ℝ}
    (hnum : TendstoInDistribution
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω))
      atTop Gnum (fun _ => μ) ν)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hsigma_ne : errorVariance μ e ≠ 0) :
    TwoSLSSubsetCommonSigmaDiffConditions
      μ ν Za Zb X Y (errorVariance μ e) Gnum :=
  of_covarianceMomentConsistency
    (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (sigma2 := errorVariance μ e) hnum
    (hMaintained.toCovarianceMomentConsistencyConditions β hmodel)
    (hFull.toCovarianceMomentConsistencyConditions β hmodel)
    hsigma_ne

end TwoSLSSubsetCommonSigmaDiffConditions

/-- Bounded-numerator version of Hansen Theorem 12.17's denominator
substitution step.

The maintained Sargan numerator is used only through `O_p(1)`.  The
maintained and full residual-variance consistency hypotheses are reused from
the Chapter 12.3 covariance-moment package and give the reciprocal-variance
difference `o_p(1)`. -/
theorem twoSLSSubsetCommonSigmaDiff_tendstoInMeasure_zero_of_bounded_covarianceMomentConsistency
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZa : Matrix k la ℝ} {QZZa Omegaa : Matrix la la ℝ}
    {QZXa : Matrix la k ℝ}
    {QXZfull : Matrix k (la ⊕ lb) ℝ}
    {QZZfull Omegafull : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QZXfull : Matrix (la ⊕ lb) k ℝ}
    {sigma2 : ℝ}
    (hnum : BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)))
    (hMaintained : TwoSLSCovarianceMomentConsistencyConditions
      μ Za X e Y QXZa QZZa Omegaa QZXa sigma2)
    (hFull : TwoSLSCovarianceMomentConsistencyConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y
        QXZfull QZZfull Omegafull QZXfull sigma2)
    (hsigma_ne : sigma2 ≠ 0) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) := by
  have hmaintainedInv : TendstoInMeasure μ
      (fun m ω =>
        (twoSLSSigmaSqHatStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω))⁻¹)
      atTop (fun _ => sigma2⁻¹) :=
    tendstoInMeasure_inv_const_real hMaintained.sigma_meas
      hMaintained.sigma_tendsto hsigma_ne
  have hfullInv : TendstoInMeasure μ
      (fun m ω =>
        (twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))⁻¹)
      atTop (fun _ => sigma2⁻¹) :=
    tendstoInMeasure_inv_const_real
      (by
        intro m
        simpa [stackRegressors, Matrix.fromCols] using hFull.sigma_meas m)
      (by simpa [stackRegressors, Matrix.fromCols] using hFull.sigma_tendsto)
      hsigma_ne
  exact
    twoSLSSubsetCommonSigmaMinusSarganDiff_tendsto_zero_of_maintainedNum_bounded_sigmaInv
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (sigmaInv := sigma2⁻¹) hnum hmaintainedInv hfullInv

/-- Assumption 12.2 facade for the bounded-numerator denominator-substitution
step in Hansen Theorem 12.17.

This version no longer asks for a maintained-numerator distributional limit
when the proof only needs tightness. -/
theorem twoSLSSubsetCommonSigmaDiff_tendstoInMeasure_zero_of_assumption12_2_bounded
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (hnum : BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)))
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hsigma_ne : errorVariance μ e ≠ 0) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) :=
  twoSLSSubsetCommonSigmaDiff_tendstoInMeasure_zero_of_bounded_covarianceMomentConsistency
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (sigma2 := errorVariance μ e) hnum
    (hMaintained.toCovarianceMomentConsistencyConditions β hmodel)
    (hFull.toCovarianceMomentConsistencyConditions β hmodel)
    hsigma_ne

private theorem boundedInProbability_of_div_tendstoInDistribution_sigma
    {S Num Sigma : ℕ → Ω → ℝ} {G : Ωlim → ℝ} {sigma2 : ℝ}
    (hS : TendstoInDistribution S atTop G (fun _ => μ) ν)
    (hSigma : TendstoInMeasure μ Sigma atTop (fun _ => sigma2))
    (hsigma_pos : 0 < sigma2)
    (hNum_eq : ∀ n ω, Sigma n ω ≠ 0 → Num n ω = S n ω * Sigma n ω) :
    BoundedInProbability μ Num := by
  have hS_bounded : BoundedInProbability μ S :=
    BoundedInProbability.of_tendstoInDistribution hS
  have hSigma_bounded : BoundedInProbability μ Sigma :=
    BoundedInProbability.of_tendstoInMeasure_const hSigma
  have hprod_bounded : BoundedInProbability μ (fun n ω => S n ω * Sigma n ω) :=
    hS_bounded.mul hSigma_bounded
  rw [tendstoInMeasure_iff_dist] at hSigma
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' ENNReal.ofNat_ne_top
  rcases hprod_bounded (δ / 2) hδ2 with ⟨M, hMpos, hM⟩
  refine ⟨M, hMpos, ?_⟩
  have heps : 0 < sigma2 / 2 := by linarith
  have hbad := (hSigma (sigma2 / 2) heps).eventually_lt_const hδ2
  filter_upwards [hM, hbad] with n hMtail hbadtail
  have hcover :
      {ω | M ≤ ‖Num n ω‖} ⊆
        {ω | M ≤ ‖S n ω * Sigma n ω‖} ∪
          {ω | sigma2 / 2 ≤ dist (Sigma n ω) sigma2} := by
    intro ω hω
    by_cases hbadω : sigma2 / 2 ≤ dist (Sigma n ω) sigma2
    · exact Or.inr hbadω
    · left
      have hsigma_ne : Sigma n ω ≠ 0 := by
        intro hsigma_zero
        have hdist : dist (Sigma n ω) sigma2 = sigma2 := by
          simp [hsigma_zero, Real.dist_eq, abs_of_pos hsigma_pos]
        exact hbadω (by rw [hdist]; linarith)
      simpa [hNum_eq n ω hsigma_ne] using hω
  calc
    μ {ω | M ≤ ‖Num n ω‖}
        ≤ μ ({ω | M ≤ ‖S n ω * Sigma n ω‖} ∪
          {ω | sigma2 / 2 ≤ dist (Sigma n ω) sigma2}) :=
          measure_mono hcover
    _ ≤ μ {ω | M ≤ ‖S n ω * Sigma n ω‖} +
          μ {ω | sigma2 / 2 ≤ dist (Sigma n ω) sigma2} :=
          measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hMtail (le_of_lt hbadtail)
    _ = δ := ENNReal.add_halves δ

omit [Fintype lb] [DecidableEq lb] in
/-- If the Sargan statistic is weakly convergent and its residual-variance
denominator is consistent for a positive scalar, then the raw Sargan numerator
is `O_p(1)`.

This is the totalized-division bridge used in Hansen Theorem 12.17 to derive
the maintained numerator tightness required by the common-denominator
Sargan-difference Slutsky step. -/
theorem twoSLSSarganNumeratorStar_boundedInProbability_of_stat_sigma
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {G : Ωlim → ℝ} {sigma2 : ℝ}
    (hstat : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν)
    (hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => sigma2))
    (hsigma_pos : 0 < sigma2) :
    BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Z m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)) := by
  exact
    boundedInProbability_of_div_tendstoInDistribution_sigma
      (μ := μ) (ν := ν)
      (S := fun m ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Num := fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Z m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω))
      (Sigma := fun m ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      hstat hsigma hsigma_pos
      (fun m ω hsigma_ne => by
        dsimp [twoSLSSarganStatOrZero]
        exact (div_mul_cancel₀
          (twoSLSSarganNumeratorStar
            (stackRegressors Z m ω) (stackRegressors X m ω)
            (stackOutcomes Y m ω))
          hsigma_ne).symm)

omit [IsProbabilityMeasure μ] in
/-- Projection/rank law bridge for Hansen Theorem 12.16.

If the limiting instrument-error score covariance factors as `B Bᵀ`, and the
pullback of the Sargan limiting quadratic form through `B` is Hermitian,
idempotent, and rank `df`, then the residual-maker quadratic form has the
corresponding chi-square law. -/
theorem twoSLSOveridPopulationResidualMaker_quadratic_hasLaw_chiSquared_of_factor_symmIdem
    {Z : ℕ → Ω → l → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {df : ℕ} [Fact (0 < df)]
    {B : Matrix l l ℝ}
    (hcov : scoreCovMat μ Z e = B * Bᵀ)
    (hH : (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B).IsHermitian)
    (hI : IsIdempotentElem
      (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B))
    (hrank : (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B).rank = df) :
    HasLaw
      (fun z : EuclideanSpace ℝ l =>
        let g := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX *ᵥ z.ofLp
        g ⬝ᵥ ((sigma2 • QZZ)⁻¹ *ᵥ g))
      (chiSquared df) (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
  let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let V := sigma2 • QZZ
  let A := twoSLSOveridLimitCriterionMatrix QXZ QZZ QZX sigma2
  have hRankA : (Bᵀ * A * B).rank = df := by
    simpa [A, twoSLSOveridLimitCriterionPullback] using hrank
  have hraw :
      HasLaw
        (fun z : EuclideanSpace ℝ l => (z : l → ℝ) ⬝ᵥ (A *ᵥ (z : l → ℝ)))
        (chiSquared (Bᵀ * A * B).rank) (multivariateGaussian 0 (B * Bᵀ)) :=
    hasLaw_multivariateGaussian_zero_quadratic_of_factor_symmIdem
      (B := B) (A := A)
      (by simpa [A, twoSLSOveridLimitCriterionPullback] using hH)
      (by simpa [A, twoSLSOveridLimitCriterionPullback] using hI)
      (by rw [hRankA]; exact Fact.out)
  have hrawdf :
      HasLaw
        (fun z : EuclideanSpace ℝ l => (z : l → ℝ) ⬝ᵥ (A *ᵥ (z : l → ℝ)))
        (chiSquared df) (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
    simpa [← hcov, hRankA] using hraw
  refine hrawdf.congr ?_
  filter_upwards with z
  dsimp [A, twoSLSOveridLimitCriterionMatrix, M, V]
  exact (quadraticForm_mulVec_eq_pullback_rect
    (B := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX)
    (A := (sigma2 • QZZ)⁻¹) (x := z.ofLp))

set_option maxHeartbeats 1200000 in
-- The measurability branch expands the residual-maker through the 2SLS
-- linearization matrix before the distributional Slutsky step.
/-- Normalized residual-maker score CLT for Hansen Theorem 12.16.

The theorem composes Chapter 7's instrument-error score CLT with the
sample-moment CMT for Hansen's residual-maker matrix
`I - Q̂_ZX (Q̂_XZ Q̂_ZZ⁻¹ Q̂_ZX)⁻¹ Q̂_XZ Q̂_ZZ⁻¹`.  It is the stochastic
residual-score input used before the final projection/rank chi-square
identification. -/
theorem twoSLSOveridResidualMakerScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSOveridResidualMakerScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun z : EuclideanSpace ℝ l =>
        ((1 : Matrix l l ℝ) -
            QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
  let M : Matrix l l ℝ :=
    (1 : Matrix l l ℝ) -
      QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹
  have hT : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω))
      atTop (fun z : EuclideanSpace ℝ l => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
    exact scoreVector_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
      (μ := μ) (X := Z) (e := e) hScore
  have hM_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          twoSLSOveridResidualMaker
            (stackRegressors Z n ω) (stackRegressors X n ω)) μ := by
    intro n
    have hprod : AEStronglyMeasurable
        (fun ω =>
          sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) *
            twoSLSLinearizationMatrix
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        ((hMom.qzx_meas n).prodMk (hMom.linearization_meas n))
    have hsub : AEStronglyMeasurable
        (fun ω =>
          (1 : Matrix l l ℝ) -
            sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) *
              twoSLSLinearizationMatrix
                (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)) μ :=
      (continuous_const.sub continuous_id).comp_aestronglyMeasurable hprod
    simpa [twoSLSOveridResidualMaker, twoSLSLinearizationMatrix,
      stackRegressors, Matrix.mul_assoc] using hsub
  have hM : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOveridResidualMaker
          (stackRegressors Z n ω) (stackRegressors X n ω))
      atTop (fun _ => M) := by
    simpa [M] using
      twoSLSOveridResidualMaker_tendstoInMeasure_of_sample_moments
        (μ := μ) (Z := Z) (X := X) (e := e) hMom
  have hSlutsky :=
    matrixMulVec_tendstoInDistribution_of_vector_and_matrix
      (μ := μ) (ν := multivariateGaussian 0 (scoreCovMat μ Z e))
      (q := l)
      (T := fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω))
      (Z := fun z : EuclideanSpace ℝ l => z.ofLp)
      (Ahat := fun n ω =>
        twoSLSOveridResidualMaker
          (stackRegressors Z n ω) (stackRegressors X n ω))
      (A := M)
      hT hM_meas hM
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hSlutsky
  intro n
  exact ae_of_all μ (fun ω => by
    have hscore :
        Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω) =
          (Real.sqrt (n : ℝ))⁻¹ •
            ((stackRegressors Z n ω)ᵀ *ᵥ stackErrors e n ω) := by
      unfold sampleCrossMoment
      rw [Fintype.card_fin]
      by_cases hn : n = 0
      · subst n
        simp
      · have hnpos : 0 < (n : ℝ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 hnpos)
        have hscale :
            Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
              (Real.sqrt (n : ℝ))⁻¹ := by
          have hsqr_mul :
              Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
            Real.mul_self_sqrt hnpos.le
          calc
            Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
                Real.sqrt (n : ℝ) *
                  (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ))⁻¹ := by
              rw [hsqr_mul]
            _ = (Real.sqrt (n : ℝ))⁻¹ := by
              field_simp [hsqrt_ne]
        simp [smul_smul, hscale]
    change
      twoSLSOveridResidualMaker (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω)) =
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSOveridResidualMakerScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackErrors e n ω)
    rw [hscore]
    simp [twoSLSOveridResidualMakerScoreStar, Matrix.mulVec_smul])

/-- Normalized feasible residual-score CLT for Hansen Theorem 12.16.

The structural-model residual score `n^{-1/2} Z' ê` has the same distributional
limit as the true-error residual-maker score.  The equality holds on the
nonsingular sample-bread event, and that event has asymptotically full
probability under the sample-moment package. -/
theorem twoSLSSarganResidualScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop
      (fun z : EuclideanSpace ℝ l =>
        ((1 : Matrix l l ℝ) -
            QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
  let overidScore : ℕ → Ω → l → ℝ := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ •
      twoSLSOveridResidualMakerScoreStar
        (stackRegressors Z n ω) (stackRegressors X n ω) (stackErrors e n ω)
  let residualScore : ℕ → Ω → l → ℝ := fun n ω =>
    (Real.sqrt (n : ℝ))⁻¹ •
      twoSLSSarganResidualScoreStar
        (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)
  let M : Matrix l l ℝ :=
    (1 : Matrix l l ℝ) -
      QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹
  have hoverid : TendstoInDistribution overidScore atTop
      (fun z : EuclideanSpace ℝ l => M *ᵥ z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
    simpa [overidScore, M] using
      twoSLSOveridResidualMakerScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT
        (μ := μ) (Z := Z) (X := X) (e := e) hMom hScore
  have hdiff : TendstoInMeasure μ (residualScore - overidScore)
      atTop (fun _ => 0) := by
    have hsingular :=
      measure_twoSLSBread_singular_tendsto_zero_of_sample_moments
        (μ := μ) (Z := Z) (X := X) (e := e) hMom
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsingular
      (Eventually.of_forall (fun _ => zero_le _)) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn_pos
    refine measure_mono ?_
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro hbread
    haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
    have hstar_unit :
        IsUnit
          (twoSLSMomentMatrixStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det :=
      isUnit_twoSLSMomentMatrixStar_det_of_sample_bread
        (Z := fun i : Fin n => Z i.val ω)
        (X := fun i : Fin n => X i.val ω) hbread
    have hY :
        stackOutcomes Y n ω =
          stackRegressors X n ω *ᵥ β + stackErrors e n ω :=
      stack_linear_model X e Y β hmodel n ω
    have hR : residualScore n ω - overidScore n ω = 0 := by
      dsimp [residualScore, overidScore]
      rw [hY]
      rw [twoSLSSarganResidualScoreStar_linear_model_eq_overidResidualMaker
        (Z := stackRegressors Z n ω) (X := stackRegressors X n ω)
        (β := β) (e := stackErrors e n ω) (hunit := hstar_unit)]
      simp [twoSLSOveridResidualMakerScoreStar]
    change ε ≤ edist ((residualScore n ω - overidScore n ω)) 0 at hω
    rw [hR, edist_self] at hω
    exact absurd hω (not_le.mpr hε)
  have hres_meas' : ∀ n, AEMeasurable (residualScore n) μ := by
    intro n
    simpa [residualScore] using hres_meas n
  simpa [residualScore, M] using
    tendstoInDistribution_of_tendstoInMeasure_sub
      (X := overidScore)
      (Y := residualScore)
      (Z := fun z : EuclideanSpace ℝ l => M *ᵥ z.ofLp)
      hoverid hdiff hres_meas'

set_option linter.style.longLine false in
/-- Subset residualized-score CLT from the existing Theorem 12.16 full-score
CLT route.

The full-instrument residual score is supplied by
`twoSLSSarganResidualScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model`;
this theorem only adds the residualized-score map Slutsky step. -/
theorem
    twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model_fullResidualScoreMap_eventuallyAE
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k (la ⊕ lb) ℝ} {QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QZX : Matrix (la ⊕ lb) k ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hFullScore_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za n ω) (stackRegressors Zb n ω))
            (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hrank : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hTarget_meas : ∀ m : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A)) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
        A *ᵥ
          (((1 : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp))
      (fun _ => μ)
      (multivariateGaussian 0
        (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hFullScore :
      TendstoInDistribution
        (fun (m : ℕ) (ω : Ω) =>
          (Real.sqrt (m : ℝ))⁻¹ •
            twoSLSSarganResidualScoreStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) (stackOutcomes Y m ω))
        atTop
        (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
          ((1 : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp)
        (fun _ => μ)
        (multivariateGaussian 0
          (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)) := by
    have hraw :=
      twoSLSSarganResidualScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model
        (μ := μ) (Z := Zfull) (X := X) (e := e) (Y := Y)
        hMom hScore β hmodel
        (by
          intro n
          simpa [Zfull, stackRegressors, Matrix.fromCols] using hFullScore_meas n)
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hraw
  exact
    twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_fullResidualScoreMap_eventuallyAE
      (μ := μ)
      (ν := multivariateGaussian 0
        (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e))
      (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (A := A)
      hrank hTarget_meas hA_meas hA hFullScore

set_option linter.style.longLine false in
/-- High-probability-rank companion to
`twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model_fullResidualScoreMap_eventuallyAE`. -/
theorem
    twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model_fullResidualScoreMap_rankProbability
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k (la ⊕ lb) ℝ} {QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QZX : Matrix (la ⊕ lb) k ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hFullScore_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za n ω) (stackRegressors Zb n ω))
            (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hrank : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X)
    (hTarget_meas : ∀ m : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A)) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
        A *ᵥ
          (((1 : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp))
      (fun _ => μ)
      (multivariateGaussian 0
        (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hFullScore :
      TendstoInDistribution
        (fun (m : ℕ) (ω : Ω) =>
          (Real.sqrt (m : ℝ))⁻¹ •
            twoSLSSarganResidualScoreStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) (stackOutcomes Y m ω))
        atTop
        (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
          ((1 : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp)
        (fun _ => μ)
        (multivariateGaussian 0
          (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)) := by
    have hraw :=
      twoSLSSarganResidualScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model
        (μ := μ) (Z := Zfull) (X := X) (e := e) (Y := Y)
        hMom hScore β hmodel
        (by
          intro n
          simpa [Zfull, stackRegressors, Matrix.fromCols] using hFullScore_meas n)
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hraw
  exact
    twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_fullResidualScoreMap_rankProbability
      (μ := μ)
      (ν := multivariateGaussian 0
        (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e))
      (Za := Za) (Zb := Zb) (X := X) (Y := Y) (A := A)
      hrank hTarget_meas hA_meas hA hFullScore

set_option linter.style.longLine false in
/-- Pointwise-rank compatibility wrapper for
`twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model_fullResidualScoreMap_eventuallyAE`. -/
theorem
    twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model_fullResidualScoreMap
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k (la ⊕ lb) ℝ} {QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QZX : Matrix (la ⊕ lb) k ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hFullScore_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za n ω) (stackRegressors Zb n ω))
            (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A)) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
        A *ᵥ
          (((1 : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp))
      (fun _ => μ)
      (multivariateGaussian 0
        (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hFullScore :
      TendstoInDistribution
        (fun (m : ℕ) (ω : Ω) =>
          (Real.sqrt (m : ℝ))⁻¹ •
            twoSLSSarganResidualScoreStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) (stackOutcomes Y m ω))
        atTop
        (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
          ((1 : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp)
        (fun _ => μ)
        (multivariateGaussian 0
          (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)) := by
    have hraw :=
      twoSLSSarganResidualScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model
        (μ := μ) (Z := Zfull) (X := X) (e := e) (Y := Y)
        hMom hScore β hmodel
        (by
          intro n
          simpa [Zfull, stackRegressors, Matrix.fromCols] using hFullScore_meas n)
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hraw
  exact
    twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_fullResidualScoreMap
      (μ := μ)
      (ν := multivariateGaussian 0
        (scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e))
      (Za := Za) (Zb := Zb) (X := X) (Y := Y) (A := A)
      hZa hZ hA_meas hA hFullScore

/-- Measurability of Hansen Theorem 12.16's feasible criterion covariance
`σ̂² Q̂_ZZ`, from scalar residual-variance measurability and the sample moment
package. -/
theorem twoSLSSarganCriterionCovHat_aestronglyMeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ) :
    ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω) •
          sampleQZZ (stackRegressors Z n ω)) μ := by
  intro n
  have hqzz : AEStronglyMeasurable
      (fun ω => sampleQZZ (stackRegressors Z n ω)) μ := by
    simpa [stackRegressors] using hMom.qzz_meas n
  exact (hsigma_meas n).smul hqzz

/-- Consistency of Hansen Theorem 12.16's feasible criterion covariance
`σ̂² Q̂_ZZ`.

This is the covariance side of the literal score-criterion representation of
the Sargan statistic.  It reuses the Chapter 12 sample-moment package for
`Q̂_ZZ ->p Q_ZZ` and a supplied scalar residual-variance consistency theorem for
`σ̂² ->p σ²`. -/
theorem twoSLSSarganCriterionCovHat_tendstoInMeasure_of_sigma_sample_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ} {sigma2 : ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop (fun _ => sigma2)) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω) •
          sampleQZZ (stackRegressors Z n ω))
      atTop (fun _ => sigma2 • QZZ) := by
  let sigmaHat : ℕ → Ω → ℝ := fun n ω =>
    twoSLSSigmaSqHatStar
      (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)
  let QZZhat : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    sampleQZZ (stackRegressors Z n ω)
  have hsigma_meas' : ∀ n, AEStronglyMeasurable (sigmaHat n) μ := by
    intro n
    simpa [sigmaHat] using hsigma_meas n
  have hsigma' : TendstoInMeasure μ sigmaHat atTop (fun _ => sigma2) := by
    simpa [sigmaHat] using hsigma
  have hQZZ_meas : ∀ n, AEStronglyMeasurable (QZZhat n) μ := by
    intro n
    simpa [QZZhat, stackRegressors] using hMom.qzz_meas n
  have hQZZ : TendstoInMeasure μ QZZhat atTop (fun _ => QZZ) := by
    simpa [QZZhat, stackRegressors] using hMom.qzz_tendsto
  have hpair_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (sigmaHat n ω, QZZhat n ω)) μ := by
    intro n
    exact (hsigma_meas' n).prodMk (hQZZ_meas n)
  have hpair : TendstoInMeasure μ
      (fun n ω => (sigmaHat n ω, QZZhat n ω))
      atTop (fun _ => (sigma2, QZZ)) :=
    tendstoInMeasure_prodMk hsigma' hQZZ
  have hcont : Continuous (fun p : ℝ × Matrix l l ℝ => p.1 • p.2) :=
    continuous_fst.smul continuous_snd
  have hcov := tendstoInMeasure_continuous_comp hpair_meas hpair hcont
  simpa [sigmaHat, QZZhat] using hcov

/-- Proof-facing condition package for Hansen Theorem 12.16.  The fields are
the residual-score work left after the primitive Assumption 12.2 and
conditional-homoskedasticity reductions: the Sargan statistic has its
chi-square null limit. -/
structure TwoSLSSarganConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (df : ℕ) [Fact (0 < df)] : Prop where
  overidentified : Fintype.card k < Fintype.card l
  df_eq : df = Fintype.card l - Fintype.card k
  statistic_limit : TendstoInDistribution
    (fun (m : ℕ) ω =>
      twoSLSSarganStatOrZero
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)

/-- Bridge condition package for Hansen Theorem 12.16.

This is the reusable target for the residual-score proof: once the finite-sample
Sargan statistic is identified with a canonical Wald/criterion statistic `W`
and that statistic has the existing Chapter 7--9 chi-square limit, the
textbook-facing `TwoSLSSarganConditions` follow without restating the final
Sargan limit as a primitive assumption. -/
structure TwoSLSSarganWaldBridgeConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (df : ℕ) [Fact (0 < df)] (W : ℕ → Ω → ℝ) : Prop where
  overidentified : Fintype.card k < Fintype.card l
  df_eq : df = Fintype.card l - Fintype.card k
  sargan_eq_wald : ∀ (m : ℕ) (ω : Ω),
    twoSLSSarganStatOrZero
      (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) =
    W m ω
  wald_limit : TendstoInDistribution W
    atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)

/-- Convert the residual-score/Wald bridge package into the theorem-facing
Sargan condition package. -/
theorem TwoSLSSarganWaldBridgeConditions.toSarganConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)] {W : ℕ → Ω → ℝ}
    (h : TwoSLSSarganWaldBridgeConditions μ Z X Y df W) :
    TwoSLSSarganConditions μ Z X Y df where
  overidentified := h.overidentified
  df_eq := h.df_eq
  statistic_limit := by
    refine TendstoInDistribution.congr ?_ EventuallyEq.rfl h.wald_limit
    intro m
    exact ae_of_all μ (fun ω => (h.sargan_eq_wald m ω).symm)

/-- The residual-score/Wald bridge directly gives the Sargan statistic
chi-square limit. -/
theorem TwoSLSSarganWaldBridgeConditions.statisticLimit
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)] {W : ℕ → Ω → ℝ}
    (h : TwoSLSSarganWaldBridgeConditions μ Z X Y df W) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  h.toSarganConditions.statistic_limit

/-- Build the Sargan/Wald bridge from the exact residual-score quadratic
identity.  The only remaining probabilistic input is the chi-square limit of
the score-quadratic statistic. -/
theorem TwoSLSSarganWaldBridgeConditions.of_scoreQuadraticLimit
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card l)
    (hdf : df = Fintype.card l - Fintype.card k)
    (hscore : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganScoreStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)) :
    TwoSLSSarganWaldBridgeConditions μ Z X Y df
      (fun (m : ℕ) ω =>
        twoSLSSarganScoreStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)) where
  overidentified := hover
  df_eq := hdf
  sargan_eq_wald := by
    intro m ω
    exact twoSLSSarganStatOrZero_eq_scoreStatOrZero
      (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
  wald_limit := hscore

/-- Hansen Theorem 12.16 statistic endpoint: the Sargan statistic converges to
`χ²_{ℓ-k}` under the null. -/
theorem twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)] (h : TwoSLSSarganConditions μ Z X Y df) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  h.statistic_limit

/-- Hansen Theorem 12.16 statistic endpoint from the residual-score/Wald
bridge. -/
theorem twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_waldBridge
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)] {W : ℕ → Ω → ℝ}
    (h : TwoSLSSarganWaldBridgeConditions μ Z X Y df W) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  h.statisticLimit

/-- Hansen Theorem 12.16 statistic endpoint from the exact residual-score
quadratic representation. -/
theorem twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_scoreQuadraticLimit
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card l)
    (hdf : df = Fintype.card l - Fintype.card k)
    (hscore : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganScoreStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  (TwoSLSSarganWaldBridgeConditions.of_scoreQuadraticLimit
    (μ := μ) (Z := Z) (X := X) (Y := Y) hover hdf hscore).statisticLimit

/-- Score-statistic limit for Hansen Theorem 12.16 from a Chapter 9 criterion
quadratic-form bridge.

This is the non-tautological statistic layer: instead of assuming the
Sargan score statistic already has a chi-square limit, it is enough to identify
it pointwise with a feasible criterion statistic `Tₙ' V̂ₙ⁻¹ Tₙ`, prove the
vector limit of `Tₙ`, prove covariance consistency of `V̂ₙ`, and supply the
chi-square law of the limiting quadratic form. The remaining hard Hansen work
is the projection/rank law identifying that limiting quadratic form with
`χ²(ℓ-k)`. -/
theorem twoSLSSarganScoreStatOrZero_tendstoInDistribution_chiSquared_of_criterion
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → Ω → l → ℝ} {G : Ωlim → l → ℝ}
    {Vhat : ℕ → Ω → Matrix l l ℝ} {V : Matrix l l ℝ}
    (hstat : ∀ (m : ℕ) (ω : Ω),
      twoSLSSarganScoreStatOrZero
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) =
      criterionJStatOrZero (T m ω) (Vhat m ω))
    (hT : TendstoInDistribution T atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable (Vhat m) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganScoreStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  have hcrit :
      TendstoInDistribution
        (fun m ω => criterionJStatOrZero (T m ω) (Vhat m ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := μ) (ν := ν) (df := df) (k := l)
      (T := T) (Z := G) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_nonsing hLaw
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hcrit
  intro m
  exact ae_of_all μ (fun ω => (hstat m ω).symm)

/-- Hansen Theorem 12.16 Sargan statistic limit from the criterion-form score
bridge and the exact score/Sargan algebra. -/
theorem twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_scoreCriterion
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → Ω → l → ℝ} {G : Ωlim → l → ℝ}
    {Vhat : ℕ → Ω → Matrix l l ℝ} {V : Matrix l l ℝ}
    (hover : Fintype.card k < Fintype.card l)
    (hdf : df = Fintype.card l - Fintype.card k)
    (hstat : ∀ (m : ℕ) (ω : Ω),
      twoSLSSarganScoreStatOrZero
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) =
      criterionJStatOrZero (T m ω) (Vhat m ω))
    (hT : TendstoInDistribution T atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable (Vhat m) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_scoreQuadraticLimit
    (μ := μ) (Z := Z) (X := X) (Y := Y) hover hdf
    (twoSLSSarganScoreStatOrZero_tendstoInDistribution_chiSquared_of_criterion
      (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y)
      (T := T) (G := G) (Vhat := Vhat) (V := V)
      hstat hT hV_meas hV hV_nonsing hLaw)

/-- Hansen Theorem 12.16 score-statistic limit from the literal normalized
residual score `n^{-1/2} Z'ê` and covariance estimate `σ̂² Q̂_ZZ`.

This specializes the criterion bridge using
`twoSLSSarganScoreStatOrZero_eq_criterionJStatOrZero_scaledScore`, so no
pointwise statistic-identification premise remains. -/
theorem twoSLSSarganScoreStatOrZero_tendstoInDistribution_chiSquared_of_scaledScoreCriterion
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {G : Ωlim → l → ℝ} {V : Matrix l l ℝ}
    (hscore : TendstoInDistribution
      (fun (m : ℕ) ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) •
          sampleQZZ (stackRegressors Z m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSigmaSqHatStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) •
          sampleQZZ (stackRegressors Z m ω))
      atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganScoreStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  twoSLSSarganScoreStatOrZero_tendstoInDistribution_chiSquared_of_criterion
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y)
    (T := fun (m : ℕ) ω =>
      (Real.sqrt (m : ℝ))⁻¹ •
        twoSLSSarganResidualScoreStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    (G := G)
    (Vhat := fun (m : ℕ) ω =>
      twoSLSSigmaSqHatStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) •
        sampleQZZ (stackRegressors Z m ω))
    (V := V)
    (fun m ω => by
      simpa using
        twoSLSSarganScoreStatOrZero_eq_criterionJStatOrZero_scaledScore
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    hscore hV_meas hV hV_nonsing hLaw

/-- Hansen Theorem 12.16 Sargan statistic limit from the literal normalized
residual score and covariance estimate `σ̂² Q̂_ZZ`, together with the exact
score/Sargan finite-sample identity. -/
theorem twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_scaledScoreCriterion
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {G : Ωlim → l → ℝ} {V : Matrix l l ℝ}
    (hover : Fintype.card k < Fintype.card l)
    (hdf : df = Fintype.card l - Fintype.card k)
    (hscore : TendstoInDistribution
      (fun (m : ℕ) ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) •
          sampleQZZ (stackRegressors Z m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSigmaSqHatStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) •
          sampleQZZ (stackRegressors Z m ω))
      atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_scoreCriterion
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y)
    (T := fun (m : ℕ) ω =>
      (Real.sqrt (m : ℝ))⁻¹ •
        twoSLSSarganResidualScoreStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    (G := G)
    (Vhat := fun (m : ℕ) ω =>
      twoSLSSigmaSqHatStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) •
        sampleQZZ (stackRegressors Z m ω))
    (V := V) hover hdf
    (fun m ω => by
      simpa using
        twoSLSSarganScoreStatOrZero_eq_criterionJStatOrZero_scaledScore
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    hscore hV_meas hV hV_nonsing hLaw

/-- Hansen Theorem 12.16 statistic limit from primitive sample-moment and score
inputs, plus the final limiting projection quadratic law.

This is the main non-tautological Sargan route: the normalized feasible
residual score is derived from the Chapter 7 instrument-score CLT and the
sample residual-maker CMT; the feasible covariance `σ̂²Q̂_ZZ` is derived from
residual-variance consistency and the `Q̂_ZZ` WLLN.  The only remaining
mathematical input is the textbook projection/rank law identifying the
limiting quadratic form as `χ²(df)`. -/
theorem twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_sample_moments_scoreCLT_sigma
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card l)
    (hdf : df = Fintype.card l - Fintype.card k)
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop (fun _ => sigma2))
    (hsigma_ne : sigma2 ≠ 0)
    (hLaw : HasLaw
      (fun z : EuclideanSpace ℝ l =>
        let g :=
          ((1 : Matrix l l ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp
        g ⬝ᵥ ((sigma2 • QZZ)⁻¹ *ᵥ g))
      (chiSquared df) (multivariateGaussian 0 (scoreCovMat μ Z e))) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  have hscore :
      TendstoInDistribution
        (fun (m : ℕ) ω =>
          (Real.sqrt (m : ℝ))⁻¹ •
            twoSLSSarganResidualScoreStar
              (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
        atTop
        (fun z : EuclideanSpace ℝ l =>
          ((1 : Matrix l l ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp)
        (fun _ => μ) (multivariateGaussian 0 (scoreCovMat μ Z e)) :=
    twoSLSSarganResidualScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hMom hScore β hmodel hres_meas
  have hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) •
          sampleQZZ (stackRegressors Z m ω)) μ :=
    twoSLSSarganCriterionCovHat_aestronglyMeasurable
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) hMom hsigma_meas
  have hV : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) •
          sampleQZZ (stackRegressors Z m ω))
      atTop (fun _ => sigma2 • QZZ) :=
    twoSLSSarganCriterionCovHat_tendstoInMeasure_of_sigma_sample_moments
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) hMom hsigma_meas hsigma
  exact
    twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_scaledScoreCriterion
      (μ := μ) (ν := multivariateGaussian 0 (scoreCovMat μ Z e))
      (Z := Z) (X := X) (Y := Y)
      (G := fun z : EuclideanSpace ℝ l =>
        ((1 : Matrix l l ℝ) -
            QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp)
      (V := sigma2 • QZZ) hover hdf hscore hV_meas hV
      (isUnit_det_smul_of_ne_zero hsigma_ne hMom.qzz_nonsing) hLaw

/-- Build the theorem-facing Hansen 12.16 condition package from primitive
sample-moment, score-CLT, and residual-variance inputs. -/
theorem TwoSLSSarganConditions.of_sample_moments_scoreCLT_sigma
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card l)
    (hdf : df = Fintype.card l - Fintype.card k)
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop (fun _ => sigma2))
    (hsigma_ne : sigma2 ≠ 0)
    (hLaw : HasLaw
      (fun z : EuclideanSpace ℝ l =>
        let g :=
          ((1 : Matrix l l ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp
        g ⬝ᵥ ((sigma2 • QZZ)⁻¹ *ᵥ g))
      (chiSquared df) (multivariateGaussian 0 (scoreCovMat μ Z e))) :
    TwoSLSSarganConditions μ Z X Y df where
  overidentified := hover
  df_eq := hdf
  statistic_limit :=
    twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_of_sample_moments_scoreCLT_sigma
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hover hdf hMom hScore β hmodel hres_meas
      hsigma_meas hsigma hsigma_ne hLaw

/-- Hansen Theorem 12.16 calibrated-size wrapper for the Sargan
overidentification test. -/
theorem twoSLSSarganTest_rejectionProb_tendsto_alpha
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSarganConditions μ Z X Y df)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ)
    (W := fun m ω =>
      twoSLSSarganStatOrZero
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    (q := df) (crit := crit) (alpha := alpha) hcrit
    h.statistic_limit

/-- Hansen Theorem 12.16 lower-tail critical-value convention for the
Sargan overidentification test. -/
theorem twoSLSSarganTest_rejectionProb_tendsto_alpha_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSarganConditions μ Z X Y df)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSarganTest_rejectionProb_tendsto_alpha h
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := df) (c := crit) (alpha := alpha) halpha_le_one hcrit)

/-- Hansen Theorem 12.16 statistic endpoint with the textbook degrees of
freedom fixed directly as `ℓ-k`.  The primitive Assumption 12.2 and
conditional-homoskedasticity reductions are still supplied by
`TwoSLSSarganConditions`. -/
theorem twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_card_sub
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSSarganConditions μ Z X Y (Fintype.card l - Fintype.card k)) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) :=
  twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared h

/-- Hansen Theorem 12.16 calibrated-size wrapper with the textbook
`χ²_{ℓ-k}` critical value. -/
theorem twoSLSSarganTest_rejectionProb_tendsto_alpha_card_sub
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSSarganConditions μ Z X Y (Fintype.card l - Fintype.card k))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSarganTest_rejectionProb_tendsto_alpha h hcrit

/-- Hansen Theorem 12.16 lower-tail critical-value wrapper with the textbook
`χ²_{ℓ-k}` degrees of freedom. -/
theorem twoSLSSarganTest_rejectionProb_tendsto_alpha_card_sub_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSSarganConditions μ Z X Y (Fintype.card l - Fintype.card k))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSarganTest_rejectionProb_tendsto_alpha_card_sub h
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card l - Fintype.card k) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Hansen Theorem 12.16 in its textbook-facing `χ²_{ℓ-k}` form: the Sargan
statistic has the stated null limit and the upper-tail rejection rule has
asymptotic size `α`. -/
theorem twoSLSSargan_theorem12_16
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSSarganConditions μ Z X Y (Fintype.card l - Fintype.card k))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  ⟨twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_card_sub h,
    twoSLSSarganTest_rejectionProb_tendsto_alpha_card_sub h hcrit⟩

/-- Hansen Theorem 12.16 with the lower-tail critical-value convention
`P(χ²_{ℓ-k} ≤ c) = 1 - α`. -/
theorem twoSLSSargan_theorem12_16_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSSarganConditions μ Z X Y (Fintype.card l - Fintype.card k))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  ⟨twoSLSSarganStatOrZero_tendstoInDistribution_chiSquared_card_sub h,
    twoSLSSarganTest_rejectionProb_tendsto_alpha_card_sub_lowerTail h
      halpha_le_one hcrit⟩

/-- Hansen Theorem 12.16 from primitive sample-moment, score-CLT, and
residual-variance inputs, with the textbook degrees of freedom `ℓ-k`.

This wrapper composes the residual-score CLT, covariance consistency, and
criterion-statistic CMT proved above; the remaining hypothesis is exactly the
projection/rank law for the limiting quadratic form. -/
theorem twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop (fun _ => sigma2))
    (hsigma_ne : sigma2 ≠ 0)
    (hLaw : HasLaw
      (fun z : EuclideanSpace ℝ l =>
        let g :=
          ((1 : Matrix l l ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp
        g ⬝ᵥ ((sigma2 • QZZ)⁻¹ *ᵥ g))
      (chiSquared (Fintype.card l - Fintype.card k))
      (multivariateGaussian 0 (scoreCovMat μ Z e)))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  have hover : Fintype.card k < Fintype.card l :=
    Nat.lt_of_sub_pos Fact.out
  have hcond : TwoSLSSarganConditions μ Z X Y
      (Fintype.card l - Fintype.card k) :=
    TwoSLSSarganConditions.of_sample_moments_scoreCLT_sigma
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (sigma2 := sigma2) hover rfl hMom hScore β hmodel
      hres_meas hsigma_meas hsigma hsigma_ne hLaw
  exact twoSLSSargan_theorem12_16 hcond hcrit

/-- Lower-tail critical-value version of
`twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma`. -/
theorem twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop (fun _ => sigma2))
    (hsigma_ne : sigma2 ≠ 0)
    (hLaw : HasLaw
      (fun z : EuclideanSpace ℝ l =>
        let g :=
          ((1 : Matrix l l ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp
        g ⬝ᵥ ((sigma2 • QZZ)⁻¹ *ᵥ g))
      (chiSquared (Fintype.card l - Fintype.card k))
      (multivariateGaussian 0 (scoreCovMat μ Z e)))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (sigma2 := sigma2)
    hMom hScore β hmodel hres_meas hsigma_meas hsigma hsigma_ne hLaw
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card l - Fintype.card k) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Hansen Theorem 12.16 from primitive sample-moment, score-CLT, and
residual-variance inputs, with the projection/rank law discharged through the
Hermitian-idempotent quadratic-form chi-square bridge. -/
theorem twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma_factorSymmIdem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ} {B : Matrix l l ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop (fun _ => sigma2))
    (hsigma_ne : sigma2 ≠ 0)
    (hcov : scoreCovMat μ Z e = B * Bᵀ)
    (hH : (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B).IsHermitian)
    (hI : IsIdempotentElem
      (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B))
    (hrank : (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B).rank =
      Fintype.card l - Fintype.card k)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  have hLaw : HasLaw
      (fun z : EuclideanSpace ℝ l =>
        let g :=
          ((1 : Matrix l l ℝ) -
              QZX * (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹) *ᵥ z.ofLp
        g ⬝ᵥ ((sigma2 • QZZ)⁻¹ *ᵥ g))
      (chiSquared (Fintype.card l - Fintype.card k))
      (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
    simpa [twoSLSOveridPopulationResidualMaker] using
      (twoSLSOveridPopulationResidualMaker_quadratic_hasLaw_chiSquared_of_factor_symmIdem
        (μ := μ) (Z := Z) (e := e) (QXZ := QXZ) (QZZ := QZZ)
        (QZX := QZX) (sigma2 := sigma2)
        (df := Fintype.card l - Fintype.card k) (B := B)
        hcov hH hI hrank)
  exact
    twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (sigma2 := sigma2)
      hMom hScore β hmodel hres_meas hsigma_meas hsigma hsigma_ne hLaw hcrit

/-- Hansen Theorem 12.16 using the natural homoskedastic score covariance
`scoreCovMat = σ² Q_ZZ`. The CFC square root of `σ² Q_ZZ` supplies the
Gaussian factor, while the population projection algebra discharges
Hermitian-ness, idempotence, and rank of the limiting pullback. -/
theorem twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma_sqrtCov
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop (fun _ => sigma2))
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ_pos : QZZ.PosDef)
    (hQZX_rank : Function.Injective QZX.mulVec)
    (hsigma_pos : 0 < sigma2)
    (hcov : scoreCovMat μ Z e = sigma2 • QZZ)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  let B : Matrix l l ℝ := CFC.sqrt (sigma2 • QZZ)
  have hV : (sigma2 • QZZ).PosDef := hQZZ_pos.smul hsigma_pos
  have hcov_factor : scoreCovMat μ Z e = B * Bᵀ := by
    calc
      scoreCovMat μ Z e = sigma2 • QZZ := hcov
      _ = B * Bᵀ := by
        simpa [B] using (cfcSqrt_posDef_factor hV).symm
  have hH : (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B).IsHermitian :=
    twoSLSOveridLimitCriterionPullback_isHermitian
      (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2) B hV
  have hQZZ_symm : QZZᵀ = QZZ := by
    have hHerm : QZZ.IsHermitian := hQZZ_pos.isHermitian
    simpa [Matrix.conjTranspose] using hHerm.eq
  have hQZZ_unit : IsUnit QZZ.det := (Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ_pos.isUnit
  have hBread_unit : IsUnit (twoSLSBread QXZ QZZ QZX).det :=
    isUnit_twoSLSBread_det_of_qzz_posDef_rank hQXZ hQZZ_pos hQZX_rank
  have hMidem : IsIdempotentElem
      (twoSLSOveridPopulationResidualMaker QXZ QZZ QZX) :=
    twoSLSOveridPopulationResidualMaker_idempotent hBread_unit
  have hMselfQ :
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      M * QZZ = QZZ * Mᵀ :=
    twoSLSOveridPopulationResidualMaker_weighted_selfAdjoint
      hQXZ hQZZ_symm hQZZ_unit
  have hMselfV :
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      M * (sigma2 • QZZ) = (sigma2 • QZZ) * Mᵀ := by
    dsimp
    simpa [Matrix.mul_smul, Matrix.smul_mul] using
      congrArg (fun A : Matrix l l ℝ => sigma2 • A) hMselfQ
  have hI : IsIdempotentElem
      (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B) := by
    simpa [B] using
      twoSLSOveridLimitCriterionPullback_idempotent_of_weightedSelfAdjoint
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2)
        hV hMidem hMselfV
  have hrank : (twoSLSOveridLimitCriterionPullback QXZ QZZ QZX sigma2 B).rank =
      Fintype.card l - Fintype.card k := by
    simpa [B] using
      twoSLSOveridLimitCriterionPullback_rank_sqrtCov
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2)
        hQXZ hQZZ_pos hQZX_rank hsigma_pos
  exact
    twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma_factorSymmIdem
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX)
      (sigma2 := sigma2) (B := B)
      hMom hScore β hmodel hres_meas hsigma_meas hsigma
      (ne_of_gt hsigma_pos) hcov_factor hH
      hI hrank hcrit

/-- Lower-tail critical-value version of
`twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma_sqrtCov`. -/
theorem twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma_sqrtCov_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {sigma2 : ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω))
      atTop (fun _ => sigma2))
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ_pos : QZZ.PosDef)
    (hQZX_rank : Function.Injective QZX.mulVec)
    (hsigma_pos : 0 < sigma2)
    (hcov : scoreCovMat μ Z e = sigma2 • QZZ)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma_sqrtCov
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (sigma2 := sigma2)
    hMom hScore β hmodel hres_meas hsigma_meas hsigma hQXZ hQZZ_pos
    hQZX_rank hsigma_pos hcov
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card l - Fintype.card k) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

private theorem scalar_pos_of_posDef_smul_posDef
    {ι : Type*} [Nonempty ι]
    {a : ℝ} {M : Matrix ι ι ℝ}
    (hM : M.PosDef) (hSM : (a • M).PosDef) :
    0 < a := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hdiag : 0 < (a • M) i i := Matrix.PosDef.diag_pos hSM
  have hMdiag : 0 < M i i := Matrix.PosDef.diag_pos hM
  have hmul : 0 < a * M i i := by
    simpa [Pi.smul_apply, smul_eq_mul] using hdiag
  exact pos_of_mul_pos_left hmul hMdiag.le

omit [DecidableEq k] [DecidableEq l] in
private theorem errorVariance_pos_of_assumption12_2_joint_iid_mixed_moments_homoskedastic
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e) :
    0 < errorVariance μ e := by
  classical
  let hIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e :=
    h.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Z X e :=
    hIid.toGramConditions
  have hcard_sub : 0 < Fintype.card l - Fintype.card k := Fact.out
  have hkl : Fintype.card k < Fintype.card l := by
    rwa [tsub_pos_iff_lt] at hcard_sub
  have hcard_l : 0 < Fintype.card l :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hkl
  haveI : Nonempty l := Fintype.card_pos_iff.mp hcard_l
  have hpop :
      popGram μ Z =
        twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) :=
    popGram_eq_twoSLSCombinedQZZ_popGram
      (μ := μ) (Z := Z) (X := X)
      hGram.toTwoSLSGramInstrumentMomentRankConditions.instrument_moments.int_outer
      hGram.toTwoSLSGramInstrumentMomentRankConditions.combined_gram.int_outer
  have hpop_pos : (popGram μ Z).PosDef := by
    rw [hpop]
    exact h.qzz_posDef
  have hcov_base :
      scoreCovMat μ Z e = errorVariance μ e • popGram μ Z :=
    scoreCovMat_eq_errorVariance_smul_popGram_homo
      (μ := μ) (X := Z) (e := e)
      hGram.score_clt.toSampleCLTAssumption72
      hIid.toSampleVarianceAssumption74 hZ0 hhomo
  have hsmul_pos : (errorVariance μ e • popGram μ Z).PosDef := by
    rw [← hcov_base]
    exact h.omega_posDef
  exact scalar_pos_of_posDef_smul_posDef hpop_pos hsmul_pos

omit [DecidableEq k] [DecidableEq l] in
private theorem errorVariance_pos_of_assumption12_2_observed_textbook_fourth_homoskedastic
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e) :
    0 < errorVariance μ e :=
  errorVariance_pos_of_assumption12_2_joint_iid_mixed_moments_homoskedastic
    (μ := μ) (Z := Z) (X := X) (e := e)
    h.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
    hZ0 hhomo

/-- Hansen Theorem 12.16 from the primitive joint-iid mixed-moment
Assumption 12.2 surface and conditional homoskedasticity.

This wrapper derives the sample IV moments, instrument-score CLT, feasible
residual-variance consistency, residual-score measurability, the homoskedastic
score-covariance identity, and the `ℓ-k` projection rank internally before
applying the square-root covariance Sargan theorem. -/
theorem twoSLSSargan_theorem12_16_of_assumption12_2_joint_iid_mixed_moments_homoskedastic
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    (hsigma_pos : 0 < errorVariance μ e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  let hIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e :=
    h.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Z X e :=
    hIid.toGramConditions
  let hCovMom : TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) :=
    h.toCovarianceMomentConsistencyConditions β hmodel
  have hYmeas : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hres_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (stackRegressors Z n ω) (stackRegressors X n ω) (stackOutcomes Y n ω)) μ :=
    fun n =>
      twoSLSSarganResidualScoreStar_scaled_aemeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hYmeas n
  have hQXZ :
      twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)) =
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ :=
    twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
      (μ := μ) (Z := Z) (X := X) hGram.toTwoSLSGramInstrumentMomentRankConditions.combined_gram
  have hpop :
      popGram μ Z =
        twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) :=
    popGram_eq_twoSLSCombinedQZZ_popGram
      (μ := μ) (Z := Z) (X := X)
      hGram.toTwoSLSGramInstrumentMomentRankConditions.instrument_moments.int_outer
      hGram.toTwoSLSGramInstrumentMomentRankConditions.combined_gram.int_outer
  have hcov_base :
      scoreCovMat μ Z e = errorVariance μ e • popGram μ Z :=
    scoreCovMat_eq_errorVariance_smul_popGram_homo
      (μ := μ) (X := Z) (e := e)
      hGram.score_clt.toSampleCLTAssumption72
      hIid.toSampleVarianceAssumption74 hZ0 hhomo
  have hcov :
      scoreCovMat μ Z e =
        errorVariance μ e •
          twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) := by
    rw [hcov_base, hpop]
  exact
    twoSLSSargan_theorem12_16_of_sample_moments_scoreCLT_sigma_sqrtCov
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (sigma2 := errorVariance μ e)
      hCovMom.sample_moments hGram.score_clt β hmodel hres_meas
      hCovMom.sigma_meas hCovMom.sigma_tendsto hQXZ h.qzz_posDef
      h.qzx_rank hsigma_pos hcov hcrit

/-- Lower-tail critical-value version of
`twoSLSSargan_theorem12_16_of_assumption12_2_joint_iid_mixed_moments_homoskedastic`. -/
theorem twoSLSSargan_theorem12_16_of_assumption12_2_joint_iid_mixed_moments_homoskedastic_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    (hsigma_pos : 0 < errorVariance μ e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16_of_assumption12_2_joint_iid_mixed_moments_homoskedastic
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h β hmodel hZ0 hhomo hsigma_pos
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card l - Fintype.card k) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Hansen Theorem 12.16 from the literal finite-fourth-moment iid Assumption
12.2 package and conditional homoskedasticity. -/
theorem twoSLSSargan_theorem12_16_of_assumption12_2_textbook_fourth_homoskedastic
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    (hsigma_pos : 0 < errorVariance μ e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16_of_assumption12_2_joint_iid_mixed_moments_homoskedastic
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toJointIidMixedMomentConditions β h.model hZ0 hhomo hsigma_pos hcrit

/-- Lower-tail critical-value version of
`twoSLSSargan_theorem12_16_of_assumption12_2_textbook_fourth_homoskedastic`. -/
theorem twoSLSSargan_theorem12_16_of_assumption12_2_textbook_fourth_homoskedastic_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    (hsigma_pos : 0 < errorVariance μ e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16_of_assumption12_2_textbook_fourth_homoskedastic
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h hZ0 hhomo hsigma_pos
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card l - Fintype.card k) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Hansen Theorem 12.16 from the literal observed-row finite-fourth-moment
Assumption 12.2 package and conditional homoskedasticity.

This is the textbook-facing observed-data facade; the proof engine is the
residual-row theorem reached through
`TwoSLSObservedIidFourthMomentPositiveCovarianceConditions.toResidualTextbookFourthConditions`. -/
private theorem twoSLSSargan_theorem12_16_of_assumption12_2_observed_textbook_fourth_homoskedastic
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    (hsigma_pos : 0 < errorVariance μ e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16_of_assumption12_2_textbook_fourth_homoskedastic
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toResidualTextbookFourthConditions hZ0 hhomo hsigma_pos hcrit

/-- Lower-tail critical-value version of
`twoSLSSargan_theorem12_16_of_assumption12_2_observed_textbook_fourth_homoskedastic`. -/
private theorem twoSLSSargan_theorem12_16_of_assumption12_2_observed_textbook_fourth_homoskedastic_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    (hsigma_pos : 0 < errorVariance μ e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16_of_assumption12_2_observed_textbook_fourth_homoskedastic
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h hZ0 hhomo hsigma_pos
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card l - Fintype.card k) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.16 from the literal observed-row finite-fourth-moment
Assumption 12.2 package and conditional homoskedasticity, with the scalar
variance positivity derived from `Ω > 0` rather than assumed separately. -/
theorem
    Theorem12_16.observed
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  have hsigma_pos : 0 < errorVariance μ e :=
    errorVariance_pos_of_assumption12_2_joint_iid_mixed_moments_homoskedastic
      (μ := μ) (Z := Z) (X := X) (e := e)
      h.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
      hZ0 hhomo
  exact
    twoSLSSargan_theorem12_16_of_assumption12_2_observed_textbook_fourth_homoskedastic
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h hZ0 hhomo hsigma_pos hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value version of
`Theorem12_16.observed`. -/
theorem
    Theorem12_16.observed_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  Theorem12_16.observed
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h hZ0 hhomo
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card l - Fintype.card k) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Maintained-model Sargan numerator tightness from primitive Assumption 12.2
and conditional homoskedasticity.

The proof reuses the Theorem 12.16 homoskedastic Sargan limit for the
maintained instrument block and the Chapter 12.3 residual-variance consistency
field from `TwoSLSCovarianceMomentConsistencyConditions`. -/
theorem twoSLSSarganNumeratorStar_bounded_of_assumption12_2_homoskedastic
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    (hover : Fintype.card k < Fintype.card l)
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance μ Z e)
    (hsigma_pos : 0 < errorVariance μ e) :
    BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Z m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)) := by
  letI : Fact (0 < Fintype.card l - Fintype.card k) :=
    ⟨Nat.sub_pos_of_lt hover⟩
  have hstat :
      TendstoInDistribution
        (fun (m : ℕ) ω =>
          twoSLSSarganStatOrZero
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
        atTop (fun x : ℝ => x) (fun _ => μ)
        (chiSquared (Fintype.card l - Fintype.card k)) :=
    (twoSLSSargan_theorem12_16_of_assumption12_2_joint_iid_mixed_moments_homoskedastic
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hZ0 hhomo hsigma_pos
      (crit := 0)
      (alpha := (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi (0 : ℝ)))
      rfl).1
  have hCov : TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) :=
    h.toCovarianceMomentConsistencyConditions β hmodel
  exact
    twoSLSSarganNumeratorStar_boundedInProbability_of_stat_sigma
      (μ := μ) (ν := chiSquared (Fintype.card l - Fintype.card k))
      (Z := Z) (X := X) (Y := Y)
      (G := fun x : ℝ => x) (sigma2 := errorVariance μ e)
      hstat hCov.sigma_tendsto hsigma_pos

/-- Hansen Theorem 12.16 from the residual-score/Wald bridge package. -/
theorem twoSLSSargan_theorem12_16_of_waldBridge
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    {W : ℕ → Ω → ℝ}
    (h : TwoSLSSarganWaldBridgeConditions
      μ Z X Y (Fintype.card l - Fintype.card k) W)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Ioi crit) = alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16 h.toSarganConditions hcrit

/-- Hansen Theorem 12.16 lower-tail critical-value convention from the
residual-score/Wald bridge package. -/
theorem twoSLSSargan_theorem12_16_of_waldBridge_lowerTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    {W : ℕ → Ω → ℝ}
    (h : TwoSLSSarganWaldBridgeConditions
      μ Z X Y (Fintype.card l - Fintype.card k) W)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card l - Fintype.card k)) (Set.Iic crit) =
      1 - alpha) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ)
      (chiSquared (Fintype.card l - Fintype.card k)) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSarganStatOrZero
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSargan_theorem12_16_lowerTail h.toSarganConditions halpha_le_one hcrit

/-- Eventual almost-sure sample-rank conditions for the observed-row
Theorem 12.17 facade.

The four Gram branches are required only on an `atTop` tail and only almost
surely.  In particular, this formulation does not demand invertibility of the
zero-row sample Grams. -/
structure TwoSLSSubsetEventuallyRankConditions
    (μ : Measure Ω)
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) : Prop where
  maintained_instrument : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
    Nonempty (Invertible
      ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω))
  full_instrument : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
    Nonempty (Invertible
      ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
        Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
  full_fitted : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
    Nonempty (Invertible
      ((fittedRegressorsStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω))ᵀ *
        fittedRegressorsStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)))
  maintained_fitted : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
    Nonempty (Invertible
      ((fittedRegressorsStar
          (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
        fittedRegressorsStar
          (stackRegressors Za m ω) (stackRegressors X m ω)))

private theorem measure_rawGram_singular_tendsto_zero
    {p : Type*} [Fintype p] [DecidableEq p]
    {W : ℕ → Ω → p → ℝ} {u : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ W u) :
    Tendsto
      (fun m => μ {ω | ¬ IsUnit
        (((stackRegressors W m ω)ᵀ * stackRegressors W m ω).det)})
      atTop (𝓝 0) := by
  have hsample := measure_sampleGram_singular_tendsto_zero h
  refine (tendsto_congr' ?_).mpr hsample
  filter_upwards [eventually_gt_atTop 0] with m hm
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hraw hsample_unit
    exact hraw
      (rawGram_det_isUnit_of_sampleGram_det_isUnit
        (stackRegressors W m ω) (by simpa using hm) hsample_unit)
  · intro hsample_bad hraw_unit
    exact hsample_bad
      (sampleGram_det_isUnit_of_rawGram_det_isUnit
        (stackRegressors W m ω) (by simpa using hm) hraw_unit)

namespace TwoSLSSubsetRankFailureProbabilityConditions

omit [IsProbabilityMeasure μ] in
/-- Failure of either instrument-Gram rank branch has vanishing probability. -/
theorem instrumentGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ}
    (h : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X) :
    Tendsto
      (fun m => μ (
        {ω | ¬ IsUnit
          (((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω).det)} ∪
        {ω | ¬ IsUnit
          (((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω)
              (stackRegressors Zb m ω)).det)}))
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun m =>
        μ {ω | ¬ IsUnit
          (((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω).det)} +
        μ {ω | ¬ IsUnit
          (((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω)
              (stackRegressors Zb m ω)).det)}) atTop (𝓝 0) := by
    simpa only [zero_add] using h.maintained_instrument.add h.full_instrument
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hsum
    (Eventually.of_forall fun _ => zero_le _) ?_
  exact Eventually.of_forall fun m => measure_union_le _ _

omit [IsProbabilityMeasure μ] in
/-- Failure of any finite-sample branch used by `N = C*` has vanishing
probability. -/
theorem all
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ}
    (h : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X) :
    Tendsto
      (fun m => μ (
        ({ω | ¬ IsUnit
          (((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω).det)} ∪
        {ω | ¬ IsUnit
          (((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω)
              (stackRegressors Zb m ω)).det)}) ∪
        ({ω | ¬ IsUnit
          (twoSLSBread
            (sampleQXZ (stackRegressors Za m ω) (stackRegressors X m ω))
            (sampleQZZ (stackRegressors Za m ω))
            (sampleQZX (stackRegressors Za m ω) (stackRegressors X m ω))).det} ∪
        {ω | ¬ IsUnit
          (twoSLSBread
            (sampleQXZ
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))
            (sampleQZZ
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
            (sampleQZX
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))).det})))
      atTop (𝓝 0) := by
  have hleft := h.instrumentGrams
  have hright : Tendsto
      (fun m => μ (
        {ω | ¬ IsUnit
          (twoSLSBread
            (sampleQXZ (stackRegressors Za m ω) (stackRegressors X m ω))
            (sampleQZZ (stackRegressors Za m ω))
            (sampleQZX (stackRegressors Za m ω) (stackRegressors X m ω))).det} ∪
        {ω | ¬ IsUnit
          (twoSLSBread
            (sampleQXZ
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))
            (sampleQZZ
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
            (sampleQZX
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))).det}))
      atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun m =>
          μ {ω | ¬ IsUnit
            (twoSLSBread
              (sampleQXZ (stackRegressors Za m ω) (stackRegressors X m ω))
              (sampleQZZ (stackRegressors Za m ω))
              (sampleQZX (stackRegressors Za m ω)
                (stackRegressors X m ω))).det} +
          μ {ω | ¬ IsUnit
            (twoSLSBread
              (sampleQXZ
                (Matrix.fromCols (stackRegressors Za m ω)
                  (stackRegressors Zb m ω)) (stackRegressors X m ω))
              (sampleQZZ
                (Matrix.fromCols (stackRegressors Za m ω)
                  (stackRegressors Zb m ω)))
              (sampleQZX
                (Matrix.fromCols (stackRegressors Za m ω)
                  (stackRegressors Zb m ω))
                (stackRegressors X m ω))).det}) atTop (𝓝 0) := by
      simpa only [zero_add] using h.maintained_bread.add h.full_bread
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hsum
      (Eventually.of_forall fun _ => zero_le _) ?_
    exact Eventually.of_forall fun m => measure_union_le _ _
  have hsum : Tendsto
      (fun m =>
        μ (
          {ω | ¬ IsUnit
            (((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω).det)} ∪
          {ω | ¬ IsUnit
            (((Matrix.fromCols (stackRegressors Za m ω)
                (stackRegressors Zb m ω))ᵀ *
              Matrix.fromCols (stackRegressors Za m ω)
                (stackRegressors Zb m ω)).det)}) +
        μ (
          {ω | ¬ IsUnit
            (twoSLSBread
              (sampleQXZ (stackRegressors Za m ω) (stackRegressors X m ω))
              (sampleQZZ (stackRegressors Za m ω))
              (sampleQZX (stackRegressors Za m ω)
                (stackRegressors X m ω))).det} ∪
          {ω | ¬ IsUnit
            (twoSLSBread
              (sampleQXZ
                (Matrix.fromCols (stackRegressors Za m ω)
                  (stackRegressors Zb m ω)) (stackRegressors X m ω))
              (sampleQZZ
                (Matrix.fromCols (stackRegressors Za m ω)
                  (stackRegressors Zb m ω)))
              (sampleQZX
                (Matrix.fromCols (stackRegressors Za m ω)
                  (stackRegressors Zb m ω))
                (stackRegressors X m ω))).det})) atTop (𝓝 0) := by
    simpa only [zero_add] using hleft.add hright
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hsum (Eventually.of_forall fun _ => zero_le _) ?_
  exact Eventually.of_forall fun m => measure_union_le _ _

/-- Observed-row Assumption 12.2 implies all high-probability rank branches
used by Hansen Theorem 12.17. -/
theorem of_observed_assumption12_2
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β) :
    TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let hMaintainedMixed :=
    hMaintained.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
  let hFullMixed :=
    hFull.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
  let hMaintainedCov :=
    hMaintainedMixed.toCovarianceMomentConsistencyConditions β hMaintained.model
  let hFullCov :=
    hFullMixed.toCovarianceMomentConsistencyConditions β hFull.model
  let hMaintainedGram :=
    hMaintainedMixed.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
      |>.toGramConditions
  let hFullGram :=
    hFullMixed.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
      |>.toGramConditions
  refine
    { maintained_instrument := ?_
      full_instrument := ?_
      maintained_bread := ?_
      full_bread := ?_ }
  · exact measure_rawGram_singular_tendsto_zero hMaintainedGram.instrument_moments
  · simpa [Zfull, stackRegressors, Matrix.fromCols] using
      (measure_rawGram_singular_tendsto_zero hFullGram.instrument_moments)
  · exact measure_twoSLSBread_singular_tendsto_zero_of_sample_moments
      hMaintainedCov.sample_moments
  · simpa [Zfull, stackRegressors, Matrix.fromCols] using
      (measure_twoSLSBread_singular_tendsto_zero_of_sample_moments
        hFullCov.sample_moments)

end TwoSLSSubsetRankFailureProbabilityConditions

omit [IsProbabilityMeasure μ] in
/-- The two instrument-Gram branches of the eventual sample-rank package. -/
theorem TwoSLSSubsetEventuallyRankConditions.instrumentGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ}
    (h : TwoSLSSubsetEventuallyRankConditions μ Za Zb X) :
    ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) := by
  filter_upwards [h.maintained_instrument, h.full_instrument] with m hZa hZ
  filter_upwards [hZa, hZ] with ω hZa_ω hZ_ω
  exact ⟨hZa_ω, hZ_ω⟩

omit [IsProbabilityMeasure μ] in
/-- All four branches of the eventual sample-rank package on one common
sample-size tail and one common full-measure event. -/
theorem TwoSLSSubsetEventuallyRankConditions.all
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ}
    (h : TwoSLSSubsetEventuallyRankConditions μ Za Zb X) :
    ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) ∧
        Nonempty (Invertible
          ((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))) ∧
        Nonempty (Invertible
          ((fittedRegressorsStar
              (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
            fittedRegressorsStar
              (stackRegressors Za m ω) (stackRegressors X m ω))) := by
  filter_upwards [h.maintained_instrument, h.full_instrument,
    h.full_fitted, h.maintained_fitted] with m hZa hZ hFitted hMaintainedFitted
  filter_upwards [hZa, hZ, hFitted, hMaintainedFitted] with
      ω hZa_ω hZ_ω hFitted_ω hMaintainedFitted_ω
  exact ⟨hZa_ω, hZ_ω, hFitted_ω, hMaintainedFitted_ω⟩

private theorem twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_gramBranches
    (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (X : Matrix n k ℝ) (Y : n → ℝ)
    (hZa : Nonempty (Invertible (Zaᵀ * Za)))
    (hZ : Nonempty (Invertible
      ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb)))
    (hFitted : Nonempty (Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
        fittedRegressorsStar (Matrix.fromCols Za Zb) X)))
    (hMaintainedFitted : Nonempty (Invertible
      ((fittedRegressorsStar Za X)ᵀ * fittedRegressorsStar Za X))) :
    twoSLSSubsetNeweyStatOrZero Za Zb X Y =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero Za Zb X Y := by
  classical
  rcases hZa with ⟨instZa⟩
  rcases hZ with ⟨instZ⟩
  letI : Invertible (Zaᵀ * Za) := instZa
  letI : Invertible
      ((Matrix.fromCols Za Zb)ᵀ * Matrix.fromCols Za Zb) := instZ
  have hR : Nonempty (Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb)) :=
    residualizedInstrumentsGram_invertible_of_fromCols_gram_invertible Za Zb
      ⟨instZ⟩
  have hMaintainedMoment : Nonempty (Invertible
      (twoSLSMomentMatrixStar Za X)) :=
    twoSLSMomentMatrixStar_invertible_of_fittedRegressorsStar_gram_invertible
      Za X hMaintainedFitted
  rcases hR with ⟨instR⟩
  rcases hFitted with ⟨instFitted⟩
  rcases hMaintainedMoment with ⟨instMaintainedMoment⟩
  letI : Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
        twoSLSSubsetResidualizedInstrumentsStar Za Zb) := instR
  letI : Invertible
      ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
        fittedRegressorsStar (Matrix.fromCols Za Zb) X) := instFitted
  letI : Invertible (twoSLSMomentMatrixStar Za X) := instMaintainedMoment
  rcases twoSLSSubsetDualSchurComplement_invertible_of_normalEquations Za Zb X with
    ⟨instSchur⟩
  letI : Invertible
      ((twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb -
        (twoSLSSubsetResidualizedInstrumentsStar Za Zb)ᵀ *
          fittedRegressorsStar (Matrix.fromCols Za Zb) X *
          ((fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
            fittedRegressorsStar (Matrix.fromCols Za Zb) X)⁻¹ *
          (fittedRegressorsStar (Matrix.fromCols Za Zb) X)ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar Za Zb) := instSchur
  exact
    twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_normalEquations
      Za Zb X Y
      (twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible
        (Matrix.fromCols Za Zb) X ⟨instFitted⟩)

/-- Proof-facing condition package for Hansen Theorem 12.17.  The deterministic
identity `N = C*`, the asymptotic equivalence `N - C ->p 0`, and the two
chi-square statistic limits are kept explicit so downstream work can replace
the fields with primitive Assumption 12.2 constructors. -/
structure TwoSLSSubsetOveridConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (df : ℕ) [Fact (0 < df)] : Prop where
  maintained_overidentified : Fintype.card k < Fintype.card la
  df_eq : df = Fintype.card lb
  newey_eq_common : ∀ (m : ℕ) (ω : Ω),
    twoSLSSubsetNeweyStatOrZero
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω) =
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω)
  newey_limit : TendstoInDistribution
    (fun (m : ℕ) ω =>
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)
  sargan_diff_limit : TendstoInDistribution
    (fun (m : ℕ) ω =>
      twoSLSSubsetSarganDiffStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)
  asymptotic_equivalence : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) -
      twoSLSSubsetSarganDiffStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun _ => 0)

/-- Bridge condition package for Hansen Theorem 12.17.

This package targets the exact proof decomposition in the text: prove the
deterministic identity `N = C*`, prove the common-denominator statistic has the
`χ²(ℓ_b)` limit, prove the ordinary Sargan-difference statistic has the same
limit, and prove `C* - C = o_p(1)`.  The theorem-facing
`TwoSLSSubsetOveridConditions` are then a thin consequence. -/
structure TwoSLSSubsetCommonSigmaBridgeConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (df : ℕ) [Fact (0 < df)] : Prop where
  maintained_overidentified : Fintype.card k < Fintype.card la
  df_eq : df = Fintype.card lb
  newey_eq_common : ∀ (m : ℕ) (ω : Ω),
    twoSLSSubsetNeweyStatOrZero
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω) =
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω)
  common_limit : TendstoInDistribution
    (fun (m : ℕ) ω =>
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)
  sargan_diff_limit : TendstoInDistribution
    (fun (m : ℕ) ω =>
      twoSLSSubsetSarganDiffStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)
  common_minus_sargan_diff_tendstoInMeasure_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) -
      twoSLSSubsetSarganDiffStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun _ => 0)

/-- Build the exact common-denominator bridge from finite-sample algebra
obligations below the final statistic equality. -/
theorem TwoSLSSubsetCommonSigmaBridgeConditions.of_finiteSampleAlgebra
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (halg : ∀ (m : ℕ) (ω : Ω),
      TwoSLSSubsetFiniteSampleAlgebra
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (hcommon : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df))
    (hsargan : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df))
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaBridgeConditions μ Za Zb X Y df where
  maintained_overidentified := hover
  df_eq := hdf
  newey_eq_common := fun m ω =>
    (halg m ω).neweyStat_eq_commonSigmaStat
  common_limit := hcommon
  sargan_diff_limit := hsargan
  common_minus_sargan_diff_tendstoInMeasure_zero := hdiff

/-- Slutsky bridge condition package for Hansen Theorem 12.17.

This is the sharper common-denominator route: the ordinary Sargan-difference
chi-square limit is derived from the common-denominator limit and
`C* - C = o_p(1)`, rather than assumed as a separate probabilistic field. -/
structure TwoSLSSubsetCommonSigmaSlutskyBridgeConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (df : ℕ) [Fact (0 < df)] : Prop where
  maintained_overidentified : Fintype.card k < Fintype.card la
  df_eq : df = Fintype.card lb
  newey_eq_common : ∀ (m : ℕ) (ω : Ω),
    twoSLSSubsetNeweyStatOrZero
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω) =
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω)
  common_limit : TendstoInDistribution
    (fun (m : ℕ) ω =>
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df)
  sargan_diff_aemeasurable : ∀ m, AEMeasurable
    (fun ω =>
      twoSLSSubsetSarganDiffStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) μ
  common_minus_sargan_diff_tendstoInMeasure_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) -
      twoSLSSubsetSarganDiffStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun _ => 0)

/-- Common-denominator subset statistic limit from a Chapter 9 criterion
quadratic-form bridge.

This is the stochastic core needed in Hansen Theorem 12.17 before the Slutsky
step from `C*` to the ordinary Sargan-difference statistic `C`. -/
theorem twoSLSSubsetSarganDiffCommonSigmaStatOrZero_tendstoInDistribution_chiSquared_of_criterion
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → Ω → lb → ℝ} {G : Ωlim → lb → ℝ}
    {Vhat : ℕ → Ω → Matrix lb lb ℝ} {V : Matrix lb lb ℝ}
    (hstat : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      criterionJStatOrZero (T m ω) (Vhat m ω))
    (hT : TendstoInDistribution T atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable (Vhat m) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  have hcrit :
      TendstoInDistribution
        (fun m ω => criterionJStatOrZero (T m ω) (Vhat m ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := μ) (ν := ν) (df := df) (k := lb)
      (T := T) (Z := G) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_nonsing hLaw
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hcrit
  intro m
  exact ae_of_all μ (fun ω => (hstat m ω).symm)

/-- Build the Slutsky common-denominator bridge from finite-sample algebra
obligations below the final statistic equality. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_finiteSampleAlgebra
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (halg : ∀ (m : ℕ) (ω : Ω),
      TwoSLSSubsetFiniteSampleAlgebra
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (hcommon : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df))
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df where
  maintained_overidentified := hover
  df_eq := hdf
  newey_eq_common := fun m ω =>
    (halg m ω).neweyStat_eq_commonSigmaStat
  common_limit := hcommon
  sargan_diff_aemeasurable := haemeas
  common_minus_sargan_diff_tendstoInMeasure_zero := hdiff

/-- Build the Slutsky common-denominator bridge from a direct limit for the
ordinary Sargan-difference statistic.

This is the reverse Slutsky orientation of the standard Hansen 12.17 route:
if `C ⇒ χ²` is already available and `C* - C = oₚ(1)`, then the
common-denominator statistic `C*` also has the same chi-square limit. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_sarganDiffLimit
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hnewey : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (hsargan : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df))
    (hcommon_aemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hsargan_aemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df where
  maintained_overidentified := hover
  df_eq := hdf
  newey_eq_common := hnewey
  common_limit :=
    tendstoInDistribution_of_tendstoInMeasure_sub
      (X := fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Y := fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Z := fun x : ℝ => x)
      hsargan hdiff hcommon_aemeas
  sargan_diff_aemeasurable := hsargan_aemeas
  common_minus_sargan_diff_tendstoInMeasure_zero := hdiff

/-- Row-measurable version of `of_sarganDiffLimit`.

The only additional work is measurability of the common-denominator statistic
`C*`, supplied by the finite-sample row-measurability lemmas above. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_sarganDiffLimit_of_rows
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hnewey : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hsargan : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df))
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_sarganDiffLimit
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
    hover hdf hnewey hsargan
    (fun m => by
      simpa [stackRegressors, stackOutcomes] using
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero_aemeasurable_of_rows
          (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
          hZa hZb hX hY m)
    (fun m => by
      simpa [stackRegressors, stackOutcomes] using
        twoSLSSubsetSarganDiffStatOrZero_aemeasurable_of_rows
          (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
          hZa hZb hX hY m)
    hdiff

/-- Build the Slutsky common-denominator bridge from finite-sample algebra
and a direct ordinary Sargan-difference limit.

This form is useful when the `N = C*` identity is already packaged as
`TwoSLSSubsetFiniteSampleAlgebra`, while the asymptotic proof has established
`C ⇒ χ²` directly. -/
theorem
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_finiteSampleAlgebra_sarganDiffLimit_of_rows
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (halg : ∀ (m : ℕ) (ω : Ω),
      TwoSLSSubsetFiniteSampleAlgebra
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (hZa : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hsargan : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df))
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_sarganDiffLimit_of_rows
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
    hover hdf (fun m ω => (halg m ω).neweyStat_eq_commonSigmaStat)
    hZa hZb hX hY hsargan hdiff

/-- Build the Slutsky common-denominator bridge when the common-denominator
statistic is identified with a Chapter 9 criterion statistic. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_commonCriterion
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → Ω → lb → ℝ} {G : Ωlim → lb → ℝ}
    {Vhat : ℕ → Ω → Matrix lb lb ℝ} {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hnewey : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (hstat : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      criterionJStatOrZero (T m ω) (Vhat m ω))
    (hT : TendstoInDistribution T atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable (Vhat m) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν)
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df where
  maintained_overidentified := hover
  df_eq := hdf
  newey_eq_common := hnewey
  common_limit :=
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero_tendstoInDistribution_chiSquared_of_criterion
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (T := T) (G := G) (Vhat := Vhat) (V := V)
      hstat hT hV_meas hV hV_nonsing hLaw
  sargan_diff_aemeasurable := haemeas
  common_minus_sargan_diff_tendstoInMeasure_zero := hdiff

/-- Build the Slutsky common-denominator bridge from the finite-sample
normal-equation hypotheses that prove Hansen's deterministic `N = C*`
identity.

Compared with `of_finiteSampleAlgebra`, this constructor no longer asks callers
to package the final statistic equality in `TwoSLSSubsetFiniteSampleAlgebra`.
It derives the equality pointwise from
`twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_normalEquations` and leaves
only the two genuinely asymptotic inputs: the common-denominator chi-square
limit and `C* - C = o_p(1)`. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hcommon : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df))
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df where
  maintained_overidentified := hover
  df_eq := hdf
  newey_eq_common := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    rcases hZ m ω with ⟨instZ⟩
    rcases hR m ω with ⟨instR⟩
    rcases hFitted m ω with ⟨instFitted⟩
    rcases hMaintainedMoment m ω with ⟨instMaintained⟩
    rcases hSchur m ω with ⟨instSchur⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instZ
    letI : Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instR
    letI : Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω)) := instFitted
    letI : Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω)) := instMaintained
    letI : Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instSchur
    exact
      twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_normalEquations
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) (hunit m ω)
  common_limit := hcommon
  sargan_diff_aemeasurable := haemeas
  common_minus_sargan_diff_tendstoInMeasure_zero := hdiff

/-- Build the Slutsky common-denominator bridge from Hansen's finite-sample
normal-equation hypotheses and a criterion-statistic proof of the
common-denominator chi-square limit.

This is the most concrete reusable constructor for Theorem 12.17 currently in
the file: the deterministic `N = C*` identity is derived from normal equations,
and the stochastic `C* ⇒ χ²` input is reduced to a subset-score CLT, covariance
consistency, and limiting quadratic-form law through Chapter 9's criterion CMT. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_commonCriterion
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → Ω → lb → ℝ} {G : Ωlim → lb → ℝ}
    {Vhat : ℕ → Ω → Matrix lb lb ℝ} {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hstat : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      criterionJStatOrZero (T m ω) (Vhat m ω))
    (hT : TendstoInDistribution T atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable (Vhat m) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν)
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  have hcommon :
      TendstoInDistribution
        (fun (m : ℕ) ω =>
          twoSLSSubsetSarganDiffCommonSigmaStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
    twoSLSSubsetSarganDiffCommonSigmaStatOrZero_tendstoInDistribution_chiSquared_of_criterion
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (T := T) (G := G) (Vhat := Vhat) (V := V)
      hstat hT hV_meas hV hV_nonsing hLaw
  exact
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      hover hdf hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hcommon haemeas hdiff

/-- Build the Slutsky common-denominator bridge from Hansen's finite-sample
normal-equation hypotheses and the concrete residualized subset-score
criterion statistic.

Compared with `of_normalEquations_commonCriterion`, this constructor no longer
takes a generic statistic-identification premise `hstat`; it derives `C*` as
the Chapter 9 criterion statistic for the normalized residualized excluded
instrument score. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreCriterion
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {G : Ωlim → lb → ℝ} {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν)
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  let T : ℕ → Ω → lb → ℝ := fun m ω =>
    (Real.sqrt (m : ℝ))⁻¹ •
      twoSLSSubsetResidualizedScoreStar
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)
  let Vhat : ℕ → Ω → Matrix lb lb ℝ := fun m ω =>
    twoSLSSubsetNeweyCriterionCovHatStar
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω)
  have hstat : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      criterionJStatOrZero (T m ω) (Vhat m ω) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    rcases hZ m ω with ⟨instZ⟩
    rcases hR m ω with ⟨instR⟩
    rcases hFitted m ω with ⟨instFitted⟩
    rcases hMaintainedMoment m ω with ⟨instMaintained⟩
    rcases hSchur m ω with ⟨instSchur⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instZ
    letI : Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instR
    letI : Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω)) := instFitted
    letI : Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω)) := instMaintained
    letI : Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω)) := instSchur
    simpa [T, Vhat] using
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero_eq_criterionJStatOrZero_residualizedScore
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) (hunit m ω)
  exact
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_commonCriterion
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (T := T) (G := G) (Vhat := Vhat) (V := V)
      hover hdf hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hstat
      (by simpa [T] using hT)
      (by simpa [Vhat] using hV_meas)
      (by simpa [Vhat] using hV)
      hV_nonsing hLaw haemeas hdiff

/-- Residualized-score criterion constructor with ordinary Sargan-difference
measurability derived from row measurability.

This removes the theorem-facing `haemeas` side condition from the common
sample-row setup while leaving the genuine stochastic inputs unchanged: the
residualized subset-score CLT, criterion covariance consistency, limiting
quadratic-form law, and `C* - C = o_p(1)`. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreCriterion_of_rows
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {G : Ωlim → lb → ℝ} {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  have haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      twoSLSSubsetSarganDiffStatOrZero_aemeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
        hZa_meas hZb_meas hX_meas hY_meas m
  exact
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreCriterion
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (G := G) (V := V)
      hover hdf hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV_meas hV hV_nonsing hLaw haemeas hdiff

/-- Residualized-score criterion constructor with the limiting quadratic-form
law derived from a positive-definite Gaussian covariance.

This is the natural full-rank subset-score route for Hansen Theorem 12.17:
callers prove the residualized score CLT with identity Gaussian limit
`N(0,V)` and `V̂ ->p V`; the Mahalanobis `χ²_{ℓ_b}` law is then supplied by
the reusable chi-square theorem instead of as a final-law premise. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreGaussianCriterion_of_rows
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  have hV_nonsing : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det V).mp hV_pos.isUnit
  have hlb_pos : 0 < Fintype.card lb := by
    rw [← hdf]
    exact Fact.out
  have hLawCard :
      HasLaw
        (fun z : EuclideanSpace ℝ lb =>
          (z : lb → ℝ) ⬝ᵥ (V⁻¹ *ᵥ (z : lb → ℝ)))
        (chiSquared (Fintype.card lb)) (multivariateGaussian 0 V) :=
    hasLaw_multivariateGaussian_zero_mahalanobis_chiSquared_fintype
      (ι := lb) hlb_pos hV_pos
  have hLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ lb => z.ofLp ⬝ᵥ (V⁻¹ *ᵥ z.ofLp))
        (chiSquared df) (multivariateGaussian 0 V) := by
    simpa [hdf] using hLawCard
  exact
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreCriterion_of_rows
      (μ := μ) (ν := multivariateGaussian 0 V)
      (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (V := V)
      hover hdf hZa_meas hZb_meas hX_meas hY_meas
      hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV_meas hV hV_nonsing hLaw hdiff

/-- Residualized subset-score Gaussian criterion inputs for Hansen Theorem 12.17.

This package isolates the remaining subset-specific stochastic boundary:
the Gaussian CLT for `n^{-1/2} R' ê`, consistency of Newey's feasible
criterion covariance, and positive definiteness of the limiting covariance.
Assumption-12.2 and homoskedastic wrappers can then derive row measurability
and denominator replacement around this single primitive package. -/
structure TwoSLSSubsetResidualizedGaussianCriterionInputs
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Za : ℕ → Ω → la → ℝ) (Zb : ℕ → Ω → lb → ℝ)
    (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (V : Matrix lb lb ℝ) : Prop where
  score_clt : TendstoInDistribution
    (fun (m : ℕ) (ω : Ω) =>
      (Real.sqrt (m : ℝ))⁻¹ •
        twoSLSSubsetResidualizedScoreStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 V)
  covariance_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) (ω : Ω) =>
      twoSLSSubsetNeweyCriterionCovHatStar
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun _ => V)
  covariance_posDef : V.PosDef

namespace TwoSLSSubsetResidualizedGaussianCriterionInputs

set_option linter.style.longLine false in
/-- Build the residualized Gaussian criterion package from the full-instrument
residual-score CLT route used in Hansen Theorem 12.16.

This removes the subset-score CLT as a primitive input: Assumption 12.2 for the
full instrument block supplies the full residual-score CLT, and the explicit
residualized score map transports it to `n^{-1/2} R' ê`.  The remaining
subset-specific stochastic inputs are the score-map convergence, Newey
covariance consistency/positive-definiteness, and the covariance identity
identifying the linear Gaussian image as `N(0,V)`. -/
theorem of_assumption12_2_fullResidualScoreMap_eventuallyAE
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {V : Matrix lb lb ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hrank : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    (hV_eq :
      V =
        let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
          fun i ω => Sum.elim (Za i ω) (Zb i ω)
        let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
        let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
        let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
        let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
        let R : Matrix lb (la ⊕ lb) ℝ := A * M
        R * scoreCovMat μ Zfull e * Rᵀ) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y V := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let QXZ : Matrix k (la ⊕ lb) ℝ :=
    twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZX : Matrix (la ⊕ lb) k ℝ :=
    twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
  let M : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let R : Matrix lb (la ⊕ lb) ℝ := A * M
  let S : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := scoreCovMat μ Zfull e
  let hIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Zfull X e :=
    hFull.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Zfull X e :=
    hIid.toGramConditions
  have hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      hFull.x_aestronglyMeasurable hFull.e_aestronglyMeasurable hmodel
  have hZfull_meas : ∀ i, AEStronglyMeasurable (Zfull i) μ := by
    intro i
    simpa [Zfull] using hFull.z_aestronglyMeasurable i
  have hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Za i) ?_
    intro a
    have ha : AEMeasurable (fun ω => Zfull i ω (Sum.inl a)) μ :=
      (measurable_pi_apply (Sum.inl a)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using ha
  have hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zb i) ?_
    intro b
    have hb : AEMeasurable (fun ω => Zfull i ω (Sum.inr b)) μ :=
      (measurable_pi_apply (Sum.inr b)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using hb
  have hFullScore_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za n ω) (stackRegressors Zb n ω))
            (stackRegressors X n ω) (stackOutcomes Y n ω)) μ := by
    intro n
    simpa [Zfull, stackRegressors, Matrix.fromCols] using
      twoSLSSarganResidualScoreStar_scaled_aemeasurable_of_rows
        (μ := μ) (Z := Zfull) (X := X) (Y := Y)
        hZfull_meas hFull.x_aestronglyMeasurable hY_meas n
  have hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ := by
    intro m
    simpa [stackRegressors] using
      twoSLSSubsetResidualizedScoreMapStar_aestronglyMeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb)
        hZa_meas hZb_meas m
  have hTarget_meas : ∀ m : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      twoSLSSubsetResidualizedScoreStar_scaled_aemeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
        hZa_meas hZb_meas hFull.x_aestronglyMeasurable hY_meas m
  have hraw : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun z : EuclideanSpace ℝ (la ⊕ lb) => A *ᵥ (M *ᵥ z.ofLp))
      (fun _ => μ) (multivariateGaussian 0 S) := by
    simpa [Zfull, QXZ, QZZ, QZX, M, S] using
      twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model_fullResidualScoreMap_eventuallyAE
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (A := A)
        hGram.toSampleMomentConvergenceConditions hGram.score_clt β hmodel
        hFullScore_meas hrank hTarget_meas hA_meas hA
  have hS_pos : S.PosSemidef :=
    scoreCovMat_posSemidef (μ := μ) (X := Zfull) (e := e) hGram.score_clt
  have hmap :
      (multivariateGaussian 0 S).map
          (fun z : EuclideanSpace ℝ (la ⊕ lb) => A *ᵥ (M *ᵥ z.ofLp)) =
        (multivariateGaussian 0 V).map
          (fun z : EuclideanSpace ℝ lb => z.ofLp) := by
    have hV_eq' : V = R * S * Rᵀ := by
      simpa [Zfull, QXZ, QZZ, QZX, M, R, S] using hV_eq
    have hfun :
        (fun z : EuclideanSpace ℝ (la ⊕ lb) => A *ᵥ (M *ᵥ z.ofLp)) =
          (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
            (matrixContinuousLinearMap R z).ofLp) := by
      funext z
      simp [R, Matrix.mulVec_mulVec]
    calc
      (multivariateGaussian 0 S).map
          (fun z : EuclideanSpace ℝ (la ⊕ lb) => A *ᵥ (M *ᵥ z.ofLp))
          =
        (multivariateGaussian 0 S).map
          (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
            (matrixContinuousLinearMap R z).ofLp) := by rw [hfun]
      _ =
        ((multivariateGaussian 0 S).map (matrixContinuousLinearMap R)).map
          (fun z : EuclideanSpace ℝ lb => z.ofLp) := by
            rw [Measure.map_map]
            · rfl
            · exact (PiLp.continuous_ofLp 2 (fun _ : lb => ℝ)).measurable
            · exact (matrixContinuousLinearMap R).continuous.measurable
      _ = (multivariateGaussian 0 (R * S * Rᵀ)).map
          (fun z : EuclideanSpace ℝ lb => z.ofLp) := by
            rw [map_matrix_multivariateGaussian hS_pos R]
            simp [Matrix.conjTranspose_eq_transpose_of_trivial]
      _ = (multivariateGaussian 0 V).map
          (fun z : EuclideanSpace ℝ lb => z.ofLp) := by
            rw [← hV_eq']
  exact
    { score_clt :=
        tendstoInDistribution_of_limit_map_eq
          (μ := μ) (ν := multivariateGaussian 0 S)
          (η := multivariateGaussian 0 V) hraw
          (by fun_prop) hmap
      covariance_tendsto := hV
      covariance_posDef := hV_pos }

set_option linter.style.longLine false in
/-- High-probability-rank companion to
`TwoSLSSubsetResidualizedGaussianCriterionInputs.of_assumption12_2_fullResidualScoreMap_eventuallyAE`. -/
theorem of_assumption12_2_fullResidualScoreMap_rankProbability
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {V : Matrix lb lb ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hrank : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    (hV_eq :
      V =
        let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
          fun i ω => Sum.elim (Za i ω) (Zb i ω)
        let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
        let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
        let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
        let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
        let R : Matrix lb (la ⊕ lb) ℝ := A * M
        R * scoreCovMat μ Zfull e * Rᵀ) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y V := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let QXZ : Matrix k (la ⊕ lb) ℝ :=
    twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZX : Matrix (la ⊕ lb) k ℝ :=
    twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
  let M : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let R : Matrix lb (la ⊕ lb) ℝ := A * M
  let S : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := scoreCovMat μ Zfull e
  let hIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Zfull X e :=
    hFull.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Zfull X e :=
    hIid.toGramConditions
  have hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      hFull.x_aestronglyMeasurable hFull.e_aestronglyMeasurable hmodel
  have hZfull_meas : ∀ i, AEStronglyMeasurable (Zfull i) μ := by
    intro i
    simpa [Zfull] using hFull.z_aestronglyMeasurable i
  have hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Za i) ?_
    intro a
    have ha : AEMeasurable (fun ω => Zfull i ω (Sum.inl a)) μ :=
      (measurable_pi_apply (Sum.inl a)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using ha
  have hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zb i) ?_
    intro b
    have hb : AEMeasurable (fun ω => Zfull i ω (Sum.inr b)) μ :=
      (measurable_pi_apply (Sum.inr b)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using hb
  have hFullScore_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ))⁻¹ •
          twoSLSSarganResidualScoreStar
            (Matrix.fromCols (stackRegressors Za n ω) (stackRegressors Zb n ω))
            (stackRegressors X n ω) (stackOutcomes Y n ω)) μ := by
    intro n
    simpa [Zfull, stackRegressors, Matrix.fromCols] using
      twoSLSSarganResidualScoreStar_scaled_aemeasurable_of_rows
        (μ := μ) (Z := Zfull) (X := X) (Y := Y)
        hZfull_meas hFull.x_aestronglyMeasurable hY_meas n
  have hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ := by
    intro m
    simpa [stackRegressors] using
      twoSLSSubsetResidualizedScoreMapStar_aestronglyMeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) hZa_meas hZb_meas m
  have hTarget_meas : ∀ m : ℕ, AEMeasurable
      (fun ω =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      twoSLSSubsetResidualizedScoreStar_scaled_aemeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
        hZa_meas hZb_meas hFull.x_aestronglyMeasurable hY_meas m
  have hraw : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun z : EuclideanSpace ℝ (la ⊕ lb) => A *ᵥ (M *ᵥ z.ofLp))
      (fun _ => μ) (multivariateGaussian 0 S) := by
    simpa [Zfull, QXZ, QZZ, QZX, M, S] using
      twoSLSSubsetResidualizedScoreStar_scaled_tendstoInDistribution_of_sample_moments_scoreCLT_model_fullResidualScoreMap_rankProbability
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) (A := A)
        hGram.toSampleMomentConvergenceConditions hGram.score_clt β hmodel
        hFullScore_meas hrank hTarget_meas hA_meas hA
  have hS_pos : S.PosSemidef :=
    scoreCovMat_posSemidef (μ := μ) (X := Zfull) (e := e) hGram.score_clt
  have hmap :
      (multivariateGaussian 0 S).map
          (fun z : EuclideanSpace ℝ (la ⊕ lb) => A *ᵥ (M *ᵥ z.ofLp)) =
        (multivariateGaussian 0 V).map
          (fun z : EuclideanSpace ℝ lb => z.ofLp) := by
    have hV_eq' : V = R * S * Rᵀ := by
      simpa [Zfull, QXZ, QZZ, QZX, M, R, S] using hV_eq
    have hfun :
        (fun z : EuclideanSpace ℝ (la ⊕ lb) => A *ᵥ (M *ᵥ z.ofLp)) =
          (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
            (matrixContinuousLinearMap R z).ofLp) := by
      funext z
      simp [R, Matrix.mulVec_mulVec]
    calc
      (multivariateGaussian 0 S).map
          (fun z : EuclideanSpace ℝ (la ⊕ lb) => A *ᵥ (M *ᵥ z.ofLp)) =
        (multivariateGaussian 0 S).map
          (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
            (matrixContinuousLinearMap R z).ofLp) := by rw [hfun]
      _ = ((multivariateGaussian 0 S).map (matrixContinuousLinearMap R)).map
          (fun z : EuclideanSpace ℝ lb => z.ofLp) := by
            rw [Measure.map_map]
            · rfl
            · exact (PiLp.continuous_ofLp 2 (fun _ : lb => ℝ)).measurable
            · exact (matrixContinuousLinearMap R).continuous.measurable
      _ = (multivariateGaussian 0 (R * S * Rᵀ)).map
          (fun z : EuclideanSpace ℝ lb => z.ofLp) := by
            rw [map_matrix_multivariateGaussian hS_pos R]
            simp [Matrix.conjTranspose_eq_transpose_of_trivial]
      _ = (multivariateGaussian 0 V).map
          (fun z : EuclideanSpace ℝ lb => z.ofLp) := by rw [← hV_eq']
  exact
    { score_clt :=
        tendstoInDistribution_of_limit_map_eq
          (μ := μ) (ν := multivariateGaussian 0 S)
          (η := multivariateGaussian 0 V) hraw (by fun_prop) hmap
      covariance_tendsto := hV
      covariance_posDef := hV_pos }

/-- Pointwise-rank compatibility wrapper for
`of_assumption12_2_fullResidualScoreMap_eventuallyAE`. -/
theorem of_assumption12_2_fullResidualScoreMap
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {V : Matrix lb lb ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    (hV_eq :
      V =
        let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
          fun i ω => Sum.elim (Za i ω) (Zb i ω)
        let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
        let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
        let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
        let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
        let R : Matrix lb (la ⊕ lb) ℝ := A * M
        R * scoreCovMat μ Zfull e * Rᵀ) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y V :=
  of_assumption12_2_fullResidualScoreMap_eventuallyAE
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) (V := V) hFull β hmodel
    (Eventually.of_forall fun m => ae_of_all μ fun ω => ⟨hZa m ω, hZ m ω⟩)
    hA hV hV_pos hV_eq

set_option linter.style.longLine false in
/-- Build the residualized Gaussian criterion package from the full-instrument
residual-score CLT route, deriving the subset covariance positive-definiteness
from the full-score covariance and full row rank of the limiting
residualized-score map.

This is the tighter Theorem 12.17 covariance route: once the displayed
identity `V = R * Ω * R'` is proved, callers no longer need to assume `V` is
positive definite separately.  The remaining substantive inputs are the
residualized score-map convergence, Newey covariance consistency, and the
rank condition that `R = A * M` has full row rank. -/
theorem of_assumption12_2_fullResidualScoreMap_fullRowRankCovariance
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ} {V : Matrix lb lb ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M)))
    (hV_eq :
      V =
        let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
          fun i ω => Sum.elim (Za i ω) (Zb i ω)
        let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
        let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
        let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
        let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
        let R : Matrix lb (la ⊕ lb) ℝ := A * M
        R * scoreCovMat μ Zfull e * Rᵀ) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y V := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let QXZ : Matrix k (la ⊕ lb) ℝ :=
    twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZZ : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
  let QZX : Matrix (la ⊕ lb) k ℝ :=
    twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
  let M : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
  let R : Matrix lb (la ⊕ lb) ℝ := A * M
  let S : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := scoreCovMat μ Zfull e
  have hR_inj : Function.Injective (fun v : lb → ℝ => Matrix.vecMul v R) := by
    simpa [Zfull, QXZ, QZZ, QZX, M, R] using hR_fullRowRank
  have hV_pos : V.PosDef := by
    have hS : S.PosDef := by
      simpa [S, Zfull] using hFull.omega_posDef
    have hV_eq' : V = R * S * Rᵀ := by
      simpa [Zfull, QXZ, QZZ, QZX, M, R, S] using hV_eq
    have hRpos : (R * S * R.conjTranspose).PosDef :=
      Matrix.PosDef.mul_mul_conjTranspose_same hS hR_inj
    rw [hV_eq']
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hRpos
  exact
    of_assumption12_2_fullResidualScoreMap
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) (V := V)
      hFull β hmodel hZa hZ hA hV hV_pos hV_eq

set_option linter.style.longLine false in
/-- Formula-target version of
`of_assumption12_2_fullResidualScoreMap_fullRowRankCovariance`.

The limiting covariance is the canonical displayed subset covariance
`twoSLSSubsetResidualizedScoreCovariance`, so callers only prove Newey
covariance consistency to that target and full row rank of the limiting
residualized-score map. -/
theorem of_assumption12_2_fullResidualScoreMap_covarianceTarget
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) :=
  of_assumption12_2_fullResidualScoreMap_fullRowRankCovariance
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A)
    hFull β hmodel hZa hZ hA hV hR_fullRowRank
    (by
      simp [twoSLSSubsetResidualizedScoreCovariance, Matrix.transpose_mul,
        Matrix.mul_assoc])

set_option linter.style.longLine false in
/-- Row-Gram full-rank version of
`of_assumption12_2_fullResidualScoreMap_covarianceTarget`.

This exposes a common primitive rank certificate for Hansen Theorem 12.17:
nonsingularity of `(A M)(A M)'` for the limiting residualized-score map. -/
theorem of_assumption12_2_fullResidualScoreMap_covarianceTarget_rowGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_gram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) :=
  of_assumption12_2_fullResidualScoreMap_covarianceTarget
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A)
    hFull β hmodel hZa hZ hA hV
    (twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
      μ Za Zb X A hR_gram)

set_option linter.style.longLine false in
set_option maxHeartbeats 1000000 in
-- This constructor uses the explicit Newey covariance CMT bridge, so callers
-- no longer have to provide covariance consistency as a primitive field.
/-- Residualized Gaussian criterion package with Newey covariance consistency
derived from full-instrument sample moments.

The remaining covariance-side assumption is the population identity
`scoreCovMat μ [Za,Zb] e = σ² QZZ` for the full instrument block.  This is
kept explicit because the maintained-instrument homoskedasticity used in some
older 12.17 facades does not by itself identify the full-instrument score
covariance. -/
theorem of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance_eventuallyAE
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hrank : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible
          ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)) ∧
        Nonempty (Invertible
          ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let hFullIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Zfull X e :=
    hFull.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hFullGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Zfull X e :=
    hFullIid.toGramConditions
  let hCovMom : TwoSLSCovarianceMomentConsistencyConditions
      μ Zfull X e Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X)))
      (scoreCovMat μ Zfull e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X)))
      (errorVariance μ e) :=
    hFull.toCovarianceMomentConsistencyConditions β hmodel
  have hZfull_meas : ∀ i, AEStronglyMeasurable (Zfull i) μ := by
    intro i
    simpa [Zfull] using hFull.z_aestronglyMeasurable i
  have hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Za i) ?_
    intro a
    have ha : AEMeasurable (fun ω => Zfull i ω (Sum.inl a)) μ :=
      (measurable_pi_apply (Sum.inl a)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using ha
  have hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zb i) ?_
    intro b
    have hb : AEMeasurable (fun ω => Zfull i ω (Sum.inr b)) μ :=
      (measurable_pi_apply (Sum.inr b)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using hb
  have hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ := by
    intro m
    simpa [stackRegressors] using
      twoSLSSubsetResidualizedScoreMapStar_aestronglyMeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) hZa_meas hZb_meas m
  have hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    intro m
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hCovMom.sigma_meas m
  have hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => errorVariance μ e) := by
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hCovMom.sigma_tendsto
  have hQXZ :
      twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X)) =
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X)))ᵀ :=
    twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
      (μ := μ) (Z := Zfull) (X := X)
      hFullGram.toTwoSLSGramInstrumentMomentRankConditions.combined_gram
  have hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) := by
    simpa [Zfull] using
      twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_covarianceTarget_eventuallyAE
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (A := A) (sigma2 := errorVariance μ e)
        hCovMom.sample_moments hsigma_meas hsigma hA_meas hA hrank
        hQXZ hFull.qzz_posDef hcov
  exact
    of_assumption12_2_fullResidualScoreMap_eventuallyAE
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) (V := twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A)
      hFull β hmodel hrank hA hV
      (twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_fullRowRank
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (A := A)
        hFull hR_fullRowRank)
      (by
        simp [twoSLSSubsetResidualizedScoreCovariance, Matrix.transpose_mul,
          Matrix.mul_assoc])

set_option linter.style.longLine false in
set_option maxHeartbeats 1000000 in
-- This constructor combines two high-probability finite-sample identities.
/-- High-probability-rank Newey-covariance constructor for Hansen Theorem
12.17. -/
theorem of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance_rankProbability
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hrank : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let hFullIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Zfull X e :=
    hFull.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hFullGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Zfull X e :=
    hFullIid.toGramConditions
  let hCovMom : TwoSLSCovarianceMomentConsistencyConditions
      μ Zfull X e Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X)))
      (scoreCovMat μ Zfull e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X)))
      (errorVariance μ e) :=
    hFull.toCovarianceMomentConsistencyConditions β hmodel
  have hZfull_meas : ∀ i, AEStronglyMeasurable (Zfull i) μ := by
    intro i
    simpa [Zfull] using hFull.z_aestronglyMeasurable i
  have hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Za i) ?_
    intro a
    have ha : AEMeasurable (fun ω => Zfull i ω (Sum.inl a)) μ :=
      (measurable_pi_apply (Sum.inl a)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using ha
  have hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zb i) ?_
    intro b
    have hb : AEMeasurable (fun ω => Zfull i ω (Sum.inr b)) μ :=
      (measurable_pi_apply (Sum.inr b)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using hb
  have hA_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)) μ := by
    intro m
    simpa [stackRegressors] using
      twoSLSSubsetResidualizedScoreMapStar_aestronglyMeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) hZa_meas hZb_meas m
  have hsigma_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    intro m
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hCovMom.sigma_meas m
  have hsigma : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSigmaSqHatStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => errorVariance μ e) := by
    simpa [Zfull, stackRegressors, Matrix.fromCols] using hCovMom.sigma_tendsto
  have hQXZ :
      twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X)) =
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X)))ᵀ :=
    twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
      (μ := μ) (Z := Zfull) (X := X)
      hFullGram.toTwoSLSGramInstrumentMomentRankConditions.combined_gram
  have hVraw :=
    twoSLSSubsetNeweyCriterionCovHatStar_tendstoInMeasure_of_sigma_sample_moments_scoreMap_rankProbability
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) (sigma2 := errorVariance μ e)
      hCovMom.sample_moments hsigma_meas hsigma hA_meas hA hrank
  have htarget :
      twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A =
        errorVariance μ e •
          (A *
            (twoSLSOveridPopulationResidualMaker
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))) *
              twoSLSCombinedQZZ
                (popGram μ (twoSLSCombinedRegressors Zfull X))) * Aᵀ) :=
    twoSLSSubsetResidualizedScoreCovariance_eq_sigma_scoreMap_residualMaker_popGram
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e)
      (A := A) (sigma2 := errorVariance μ e)
      (by simpa [Zfull] using hQXZ)
      (by simpa [Zfull] using hFull.qzz_posDef)
      hCovMom.sample_moments.bread_nonsing (by simpa [Zfull] using hcov)
  have hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) := by
    simpa [Zfull, htarget] using hVraw
  exact
    of_assumption12_2_fullResidualScoreMap_rankProbability
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) (V := twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A)
      hFull β hmodel hrank hA hV
      (twoSLSSubsetResidualizedScoreCovariance_posDef_of_limitMap_fullRowRank
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (A := A)
        hFull hR_fullRowRank)
      (by
        simp [twoSLSSubsetResidualizedScoreCovariance, Matrix.transpose_mul,
          Matrix.mul_assoc])

/-- Pointwise-rank compatibility wrapper for
`of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance_eventuallyAE`. -/
theorem of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) :=
  of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance_eventuallyAE
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y) (A := A)
    hFull β hmodel
    (Eventually.of_forall fun m => ae_of_all μ fun ω => ⟨hZa m ω, hZ m ω⟩)
    hA hcov hR_fullRowRank

set_option linter.style.longLine false in
/-- Row-Gram version of
`of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance`. -/
theorem of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
    (hR_gram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) :=
  of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A)
    hFull β hmodel hZa hZ hA hcov
    (twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
      μ Za Zb X A hR_gram)

omit [DecidableEq k] in
set_option linter.style.longLine false in
/-- Assumption 12.2 full-instrument sample-Gram bridge for Hansen's
residualized score map.

The maintained Assumption 12.2 package supplies nonsingularity of the
maintained block `Q_aa`; the full-instrument package supplies the WLLN for
`Q = E[Z Z']` and nonsingularity of the full instrument Gram.  The conclusion
is the population-Gram expression used in Hansen Theorem 12.17. -/
theorem
    twoSLSSubsetResidualizedScoreMapStar_tendstoInMeasure_of_assumption12_2_fullInstrumentSampleGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreMapFromGram
            (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)))) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let A : Matrix lb (la ⊕ lb) ℝ :=
    twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
  let hFullIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Zfull X e :=
    hFull.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hFullGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Zfull X e :=
    hFullIid.toGramConditions
  have hGram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ := by
    intro m
    simpa [Zfull, stackRegressors, Matrix.fromCols] using
      sampleGram_stackRegressors_aestronglyMeasurable
        (μ := μ) (X := Zfull) (e := e) hFullGram.instrument_moments m
  have hGram : TendstoInMeasure μ
      (fun m ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => popGram μ Zfull) := by
    simpa [Zfull, stackRegressors, Matrix.fromCols] using
      sampleGram_stackRegressors_tendstoInMeasure_popGram
        (μ := μ) (X := Zfull) (e := e) hFullGram.instrument_moments
  let hMaintainedIidFourth :
      TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Za X e :=
    hMaintained.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hMaintainedGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Za X e :=
    hMaintainedIidFourth.toGramConditions
  have hMaintainedIid : TwoSLSSplitIidSecondMomentRankConditions μ Za X e :=
    hMaintainedIidFourth.toTwoSLSSplitIidSecondMomentRankConditions
  have hFullIidBase : TwoSLSSplitIidSecondMomentRankConditions μ Zfull X e :=
    hFullIid.toTwoSLSSplitIidSecondMomentRankConditions
  have hZaInt : Integrable (fun ω => Matrix.vecMulVec (Za 0 ω) (Za 0 ω)) μ :=
    hMaintainedGram.instrument_moments.int_outer
  have hFullInt : Integrable
      (fun ω =>
        Matrix.vecMulVec
          (Sum.elim (Za 0 ω) (Zb 0 ω))
          (Sum.elim (Za 0 ω) (Zb 0 ω))) μ := by
    simpa [Zfull] using
      hFullGram.instrument_moments.int_outer
  have hQaa : IsUnit ((popGram μ Zfull).submatrix Sum.inl Sum.inl).det := by
    rw [popGram_fullInstrument_submatrix_inl_inl
      (μ := μ) Za Zb hZaInt hFullInt]
    exact hMaintainedIid.instrument_popGram_nonsing
  have hQ : IsUnit (popGram μ Zfull).det :=
    hFullIidBase.instrument_popGram_nonsing
  simpa [A, Zfull] using
    twoSLSSubsetResidualizedScoreMapStar_tendstoInMeasure_of_fullSampleGram
      (μ := μ) (Za := Za) (Zb := Zb) (Q := popGram μ Zfull)
      hGram_meas hGram hQaa hQ

set_option linter.style.longLine false in
/-- Formula-target version deriving the residualized score-map limit from the
full-instrument sample-Gram WLLN supplied by Assumption 12.2.

The limiting score map is Hansen's population Gram expression
`(Q_b· - Q_ba Q_aa^{-1} Q_a·) Q^{-1}` for the full instrument block
`[Z_a,Z_b]`; the maintained and full Assumption 12.2 packages supply the
`Q_aa` and `Q` nonsingularity inputs, respectively. -/
theorem of_assumption12_2_fullInstrumentSampleGram_covarianceTarget
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
        (twoSLSSubsetResidualizedScoreMapFromGram
          (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let A : Matrix lb (la ⊕ lb) ℝ :=
    twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
  let hFullIid : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Zfull X e :=
    hFull.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hFullGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Zfull X e :=
    hFullIid.toGramConditions
  have hGram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))) μ := by
    intro m
    simpa [Zfull, stackRegressors, Matrix.fromCols] using
      sampleGram_stackRegressors_aestronglyMeasurable
        (μ := μ) (X := Zfull) (e := e) hFullGram.instrument_moments m
  have hGram : TendstoInMeasure μ
      (fun m ω =>
        sampleGram
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)))
      atTop (fun _ => popGram μ Zfull) := by
    simpa [Zfull, stackRegressors, Matrix.fromCols] using
      sampleGram_stackRegressors_tendstoInMeasure_popGram
        (μ := μ) (X := Zfull) (e := e) hFullGram.instrument_moments
  let hMaintainedIidFourth :
      TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Za X e :=
    hMaintained.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
  let hMaintainedGram : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Za X e :=
    hMaintainedIidFourth.toGramConditions
  have hMaintainedIid : TwoSLSSplitIidSecondMomentRankConditions μ Za X e :=
    hMaintainedIidFourth.toTwoSLSSplitIidSecondMomentRankConditions
  have hFullIidBase : TwoSLSSplitIidSecondMomentRankConditions μ Zfull X e :=
    hFullIid.toTwoSLSSplitIidSecondMomentRankConditions
  have hZaInt : Integrable (fun ω => Matrix.vecMulVec (Za 0 ω) (Za 0 ω)) μ :=
    hMaintainedGram.instrument_moments.int_outer
  have hFullInt : Integrable
      (fun ω =>
        Matrix.vecMulVec
          (Sum.elim (Za 0 ω) (Zb 0 ω))
          (Sum.elim (Za 0 ω) (Zb 0 ω))) μ := by
    simpa [Zfull] using
      hFullGram.instrument_moments.int_outer
  have hQaa : IsUnit ((popGram μ Zfull).submatrix Sum.inl Sum.inl).det := by
    rw [popGram_fullInstrument_submatrix_inl_inl
      (μ := μ) Za Zb hZaInt hFullInt]
    exact hMaintainedIid.instrument_popGram_nonsing
  have hQ : IsUnit (popGram μ Zfull).det :=
    hFullIidBase.instrument_popGram_nonsing
  have hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A) := by
    simpa [A, Zfull] using
      twoSLSSubsetResidualizedScoreMapStar_tendstoInMeasure_of_fullSampleGram
        (μ := μ) (Za := Za) (Zb := Zb) (Q := popGram μ Zfull)
        hGram_meas hGram hQaa hQ
  simpa [A, Zfull] using
    of_assumption12_2_fullResidualScoreMap_covarianceTarget
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A)
      hFull β hmodel hZa hZ hA hV hR_fullRowRank

set_option linter.style.longLine false in
/-- Row-Gram full-rank version of
`of_assumption12_2_fullInstrumentSampleGram_covarianceTarget`. -/
theorem of_assumption12_2_fullInstrumentSampleGram_covarianceTarget_rowGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_gram : IsUnit
      (let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
        (twoSLSSubsetResidualizedScoreMapFromGram
          (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))) :=
  of_assumption12_2_fullInstrumentSampleGram_covarianceTarget
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    hMaintained hFull β hmodel hZa hZ hV
    (by
      simpa [twoSLSSubsetLimitResidualizedScoreMap, Matrix.transpose_mul] using
        twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
          μ Za Zb X
          (twoSLSSubsetResidualizedScoreMapFromGram
            (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))
          hR_gram)

/-- Textbook-fourth Assumption 12.2 facade for
`of_assumption12_2_fullResidualScoreMap_covarianceTarget`.

The literal Hansen fourth-moment package supplies the full-instrument
score-CLT surface used to transport the full Sargan residual-score CLT through
the residualized-score map.  The remaining subset-specific inputs are exactly
the residualized score-map convergence, Newey covariance consistency to the
displayed target, and full row rank of the limiting residualized-score map. -/
theorem
    of_assumption12_2_textbookFourth_fullResidualScoreMap_covarianceTarget
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) :=
  of_assumption12_2_fullResidualScoreMap_covarianceTarget
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A)
    hFull.toJointIidMixedMomentConditions β hFull.model hZa hZ
    hA hV hR_fullRowRank

set_option linter.style.longLine false in
/-- Textbook-fourth row-Gram facade for the residualized Gaussian criterion
package in Hansen Theorem 12.17. -/
theorem
    of_assumption12_2_textbookFourth_fullResidualScoreMap_covarianceTarget_rowGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_gram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A) :=
  of_assumption12_2_fullResidualScoreMap_covarianceTarget_rowGram
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A)
    hFull.toJointIidMixedMomentConditions β hFull.model hZa hZ hA hV
    hR_gram

end TwoSLSSubsetResidualizedGaussianCriterionInputs

namespace TwoSLSSubsetCommonSigmaSlutskyBridgeConditions

/-- Full-rank Gaussian residualized-score constructor with denominator
substitution derived from a maintained-numerator limit and residual-variance
consistency.

This version keeps the same stochastic score and covariance inputs as
`of_normalEquations_residualizedScoreGaussianCriterion_of_rows`, but replaces
the raw `C* - C = o_p(1)` premise with
`TwoSLSSubsetCommonSigmaDiffConditions`. -/
theorem of_normalEquations_residualizedScoreGaussianCriterion_of_rows_diffConditions
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ} {sigma2 : ℝ} {Gnum : Ωlim → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    (hdiff : TwoSLSSubsetCommonSigmaDiffConditions μ ν Za Zb X Y sigma2 Gnum) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_residualizedScoreGaussianCriterion_of_rows
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
    hover hdf hZa_meas hZb_meas hX_meas hY_meas
    hZa hZ hR hFitted hMaintainedMoment hSchur hunit
    hT hV_meas hV hV_pos hdiff.tendstoInMeasure_zero

/-- Hansen Theorem 12.17 bridge from maintained/full primitive mixed-moment
Assumption 12.2 packages.

This constructor keeps the two genuinely subset-specific stochastic inputs
explicit: the residualized subset-score Gaussian CLT and Newey covariance
consistency/positive definiteness.  It derives row measurability and the
`C* - C = o_p(1)` denominator-substitution input from the maintained and full
Assumption 12.2 packages plus the maintained numerator limit. -/
theorem of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ} {Gnum : Ωlim → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hnum : TendstoInDistribution
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω))
      atTop Gnum (fun _ => μ) ν)
    (hsigma_ne : errorVariance μ e ≠ 0)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ :=
    hMaintained.z_aestronglyMeasurable
  have hX_meas : ∀ i, AEStronglyMeasurable (X i) μ :=
    hMaintained.x_aestronglyMeasurable
  have he_meas : ∀ i, AEStronglyMeasurable (e i) μ :=
    hMaintained.e_aestronglyMeasurable
  have hZfull_meas : ∀ i, AEStronglyMeasurable (Zfull i) μ := by
    intro i
    simpa [Zfull] using hFull.z_aestronglyMeasurable i
  have hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zb i) ?_
    intro b
    have hb : AEMeasurable (fun ω => Zfull i ω (Sum.inr b)) μ :=
      (measurable_pi_apply (Sum.inr b)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using hb
  have hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      hX_meas he_meas hmodel
  have hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      twoSLSSubsetNeweyCriterionCovHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
        hZa_meas hZb_meas hX_meas hY_meas m
  have hdiff :
      TwoSLSSubsetCommonSigmaDiffConditions
        μ ν Za Zb X Y (errorVariance μ e) Gnum :=
    TwoSLSSubsetCommonSigmaDiffConditions.of_assumption12_2_joint_iid_mixed_moments
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X)
      (e := e) (Y := Y) hnum hMaintained hFull β hmodel hsigma_ne
  exact
    of_normalEquations_residualizedScoreGaussianCriterion_of_rows_diffConditions
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      hover hdf hZa_meas hZb_meas hX_meas hY_meas
      hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV_meas hV hV_pos hdiff

/-- Hansen Theorem 12.17 bridge from primitive mixed-moment Assumption 12.2
packages, with the maintained-model Sargan numerator required only as
`O_p(1)`.

This matches the Slutsky denominator-replacement proof: Assumption 12.2 gives
the maintained and full residual-variance consistency, while boundedness of the
maintained numerator is the only numerator-side input needed for `C* - C =
o_p(1)`. -/
theorem of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_boundedNumerator
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hnum : BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)))
    (hsigma_ne : errorVariance μ e ≠ 0)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  have hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ :=
    hMaintained.z_aestronglyMeasurable
  have hX_meas : ∀ i, AEStronglyMeasurable (X i) μ :=
    hMaintained.x_aestronglyMeasurable
  have he_meas : ∀ i, AEStronglyMeasurable (e i) μ :=
    hMaintained.e_aestronglyMeasurable
  have hZfull_meas : ∀ i, AEStronglyMeasurable (Zfull i) μ := by
    intro i
    simpa [Zfull] using hFull.z_aestronglyMeasurable i
  have hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zb i) ?_
    intro b
    have hb : AEMeasurable (fun ω => Zfull i ω (Sum.inr b)) μ :=
      (measurable_pi_apply (Sum.inr b)).comp_aemeasurable
        (hZfull_meas i).aemeasurable
    simpa [Zfull] using hb
  have hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      hX_meas he_meas hmodel
  have hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      twoSLSSubsetNeweyCriterionCovHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
        hZa_meas hZb_meas hX_meas hY_meas m
  have hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) :=
    twoSLSSubsetCommonSigmaDiff_tendstoInMeasure_zero_of_assumption12_2_bounded
      (μ := μ) (Za := Za) (Zb := Zb) (X := X)
      (e := e) (Y := Y) hnum hMaintained hFull β hmodel hsigma_ne
  exact
    of_normalEquations_residualizedScoreGaussianCriterion_of_rows
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      hover hdf hZa_meas hZb_meas hX_meas hY_meas
      hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV_meas hV hV_pos hdiff

/-- Hansen Theorem 12.17 bridge from primitive mixed-moment Assumption 12.2
packages and conditional homoskedasticity.

Compared with
`of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_boundedNumerator`,
this constructor derives the maintained-model Sargan numerator `O_p(1)` from
the maintained Assumption 12.2 package, the structural model, and the existing
Theorem 12.16 homoskedastic Sargan limit. The residualized subset-score CLT and
Newey covariance consistency/positive-definiteness remain explicit
subset-specific inputs. -/
theorem of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_homoskedastic
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  have hnum : BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)) :=
    twoSLSSarganNumeratorStar_bounded_of_assumption12_2_homoskedastic
      (μ := μ) (Z := Za) (X := X) (e := e) (Y := Y)
      hover hMaintained β hmodel hZa0 hhomo hsigma_pos
  exact
    of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_boundedNumerator
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (V := V) hover hdf hMaintained hFull β hmodel hnum
      (ne_of_gt hsigma_pos) hZa hZ hR hFitted hMaintainedMoment hSchur
      hunit hT hV hV_pos

/-- Hansen Theorem 12.17 homoskedastic Assumption-12.2 bridge from the packaged
residualized Gaussian criterion inputs.

Compared with
`of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_homoskedastic`,
this constructor takes the residualized score CLT, Newey covariance
consistency, and covariance positive definiteness as one named theorem-facing
input package. -/
theorem of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hGaussian :
      TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y V) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_homoskedastic
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (V := V) hover hdf hMaintained hFull β hmodel hZa0 hhomo
    hsigma_pos hZa hZ hR hFitted hMaintainedMoment hSchur hunit
    hGaussian.score_clt hGaussian.covariance_tendsto hGaussian.covariance_posDef

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 homoskedastic Assumption-12.2 bridge with the
canonical displayed residualized covariance target.

This composes the full-instrument residual-score CLT constructor
`TwoSLSSubsetResidualizedGaussianCriterionInputs.of_assumption12_2_fullResidualScoreMap_covarianceTarget`
with the normal-equations Slutsky bridge.  The theorem-facing stochastic inputs
are now the residualized score-map convergence, Newey covariance consistency to
the displayed target, and full row rank of the limiting residualized score
map; positive definiteness of the subset covariance is derived from the
full-score covariance. -/
theorem of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (V := twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A)
    hover hdf hMaintained hFull β hmodel hZa0 hhomo hsigma_pos
    hZa hZ hR hFitted hMaintainedMoment hSchur hunit
    (TwoSLSSubsetResidualizedGaussianCriterionInputs.of_assumption12_2_fullResidualScoreMap_covarianceTarget
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A)
      hFull β hmodel hZa hZ hA hV hR_fullRowRank)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 homoskedastic Assumption-12.2 bridge with the
canonical displayed residualized covariance target and the dual Newey Schur
branch derived internally.

Compared with
`of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic`,
this constructor removes the separate dual Schur nonsingularity premise.  It
derives that branch from the residualized-instrument Gram, full fitted-regressor
Gram, and maintained-model moment branches via
`twoSLSSubsetDualSchurComplement_invertible_of_stackedNormalEquations`. -/
theorem of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
    hsigma_pos hZa hZ hR hFitted hMaintainedMoment
    (twoSLSSubsetDualSchurComplement_invertible_of_stackedNormalEquations
      (Za := Za) (Zb := Zb) (X := X) hZa hZ hR hFitted hMaintainedMoment)
    hunit hA hV hR_fullRowRank

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 homoskedastic Assumption-12.2 bridge where the
residualized score-map limit is derived from the full-instrument sample-Gram
WLLN.

This is the same derived-dual-Schur route as
`of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur`,
but fixes the limiting map to Hansen's displayed population-Gram expression and
discharges the former `hA` premise from the full-instrument Assumption 12.2
moment package. -/
theorem
    of_normalEquations_fullInstrumentSampleGram_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (V := twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
      (twoSLSSubsetResidualizedScoreMapFromGram
        (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)))))
    hover hdf hMaintained hFull β hmodel hZa0 hhomo hsigma_pos
    hZa hZ hR hFitted hMaintainedMoment
    (twoSLSSubsetDualSchurComplement_invertible_of_stackedNormalEquations
      (Za := Za) (Zb := Zb) (X := X) hZa hZ hR hFitted hMaintainedMoment)
    hunit
    (TwoSLSSubsetResidualizedGaussianCriterionInputs.of_assumption12_2_fullInstrumentSampleGram_covarianceTarget
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      hMaintained hFull β hmodel hZa hZ hV hR_fullRowRank)

set_option linter.style.longLine false in
/-- Row-Gram facade for
`of_normalEquations_fullInstrumentSampleGram_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur`. -/
theorem
    of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_rowGram : IsUnit
      (let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_fullInstrumentSampleGram_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    hover hdf hMaintained hFull β hmodel hZa0 hhomo hsigma_pos
    hZa hZ hR hFitted hMaintainedMoment hunit hV
    (by
      simpa [twoSLSSubsetLimitResidualizedScoreMap, Matrix.transpose_mul] using
        twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
          μ Za Zb X
          (twoSLSSubsetResidualizedScoreMapFromGram
            (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))
          hR_rowGram)

set_option linter.style.longLine false in
/-- Row-Gram facade for the homoskedastic Assumption-12.2 derived-dual-Schur
bridge.

This is the theorem-facing rank certificate Hansen's residualized Newey
covariance naturally suggests: callers may prove nonsingularity of
`(A*M)(A*M)'`; the existing full-row-rank and covariance positive-definiteness
bridges then discharge the full-rank argument internally. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
    hsigma_pos hZa hZ hR hFitted hMaintainedMoment hunit hA hV
    (twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
      μ Za Zb X A hR_rowGram)

set_option linter.style.longLine false in
/-- Full-Gram facade for the homoskedastic Assumption-12.2 derived-dual-Schur
bridge.

This derives the residualized-instrument Gram branch by Schur complement from
the maintained and full partitioned instrument Grams, leaving only the fitted
Gram, maintained moment, and full 2SLS moment determinant branches explicit. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur_fullGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  let hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      residualizedInstrumentsGram_invertible_of_fromCols_gram_invertible
        (stackRegressors Za m ω) (stackRegressors Zb m ω) (hZ m ω)
  exact
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hunit hA hV hR_rowGram

set_option linter.style.longLine false in
/-- Fitted-Gram facade for the homoskedastic Assumption-12.2 derived-dual-Schur
bridge.

This removes both finite-sample 2SLS moment inputs from the caller: the full
moment determinant branch and the maintained-model moment branch are derived
from nonsingularity of the corresponding fitted-regressor Grams. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  let hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      twoSLSMomentMatrixStar_invertible_of_fittedRegressorsStar_gram_invertible
        (stackRegressors Za m ω) (stackRegressors X m ω)
        (hMaintainedFitted m ω)
  let hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det := by
    intro m ω
    classical
    rcases hZ m ω with ⟨instZ⟩
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
      instZ
    exact
      twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible
        (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (stackRegressors X m ω) (hFitted m ω)
  exact
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hunit hA hV hR_rowGram

set_option linter.style.longLine false in
/-- Full-Gram and fitted-Gram facade for the homoskedastic Assumption-12.2
derived-dual-Schur bridge.

The residualized-instrument Gram branch is derived from the maintained/full
instrument Grams, while both 2SLS moment branches are derived from fitted
regressor Grams. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  let hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      residualizedInstrumentsGram_invertible_of_fromCols_gram_invertible
        (stackRegressors Za m ω) (stackRegressors Zb m ω) (hZ m ω)
  exact
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedFitted hA hV hR_rowGram

/-- Textbook-fourth Assumption 12.2 facade for the final homoskedastic
Theorem 12.17 bridge.

This version keeps Hansen's literal fourth-moment package at the boundary and
reuses the mixed-moment constructor internally.  It also keeps the tightened
pieces from the derived-dual-Schur route: maintained-numerator tightness,
`C* - C = o_p(1)`, the residualized subset-score CLT from the full residual
score, covariance positive-definiteness, and the dual Schur branch are all
derived rather than supplied as primitive fields. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (V := twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A)
    hover hdf hMaintained.toJointIidMixedMomentConditions
    hFull.toJointIidMixedMomentConditions β hMaintained.model hZa0 hhomo
    hsigma_pos hZa hZ hR hFitted hMaintainedMoment
    (twoSLSSubsetDualSchurComplement_invertible_of_stackedNormalEquations
      (Za := Za) (Zb := Zb) (X := X) hZa hZ hR hFitted hMaintainedMoment)
    hunit
    (TwoSLSSubsetResidualizedGaussianCriterionInputs.of_assumption12_2_textbookFourth_fullResidualScoreMap_covarianceTarget
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A)
      hFull hZa hZ hA hV hR_fullRowRank)

set_option linter.style.longLine false in
/-- Textbook-fourth row-Gram facade for the final homoskedastic Theorem 12.17
bridge.

This version keeps the literal finite-fourth Assumption 12.2 packages at the
boundary and accepts the nonsingular limiting residualized-score row Gram
instead of the equivalent full-row-rank map condition. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
    hZa hZ hR hFitted hMaintainedMoment hunit hA hV
    (twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
      μ Za Zb X A hR_rowGram)

set_option linter.style.longLine false in
/-- Textbook-fourth full-Gram and fitted-Gram facade for the final
homoskedastic Theorem 12.17 bridge.

This version keeps Hansen's literal finite-fourth Assumption 12.2 package at
the boundary while deriving the residualized-instrument Gram branch and both
2SLS moment branches from Gram regularity certificates. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df :=
  of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) hover hdf hMaintained.toJointIidMixedMomentConditions
    hFull.toJointIidMixedMomentConditions β hMaintained.model hZa0 hhomo
    hsigma_pos hZa hZ hFitted hMaintainedFitted hA hV hR_rowGram

set_option linter.style.longLine false in
/-- Textbook-fourth full-Gram/fitted-Gram facade that derives Newey covariance
consistency from full-instrument sample moments.

Compared with
`of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams`,
this version replaces the primitive covariance-convergence premise by the
population full-instrument score covariance identity
`scoreCovMat μ [Za,Zb] e = σ² QZZ`. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  let hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      residualizedInstrumentsGram_invertible_of_fromCols_gram_invertible
        (stackRegressors Za m ω) (stackRegressors Zb m ω) (hZ m ω)
  let hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      twoSLSMomentMatrixStar_invertible_of_fittedRegressorsStar_gram_invertible
        (stackRegressors Za m ω) (stackRegressors X m ω)
        (hMaintainedFitted m ω)
  let hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det := by
    intro m ω
    classical
    rcases hZ m ω with ⟨instZ⟩
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
      instZ
    exact
      twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible
        (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (stackRegressors X m ω) (hFitted m ω)
  exact
    of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (V := twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A)
      hover hdf hMaintained.toJointIidMixedMomentConditions
      hFull.toJointIidMixedMomentConditions β hMaintained.model hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment
      (twoSLSSubsetDualSchurComplement_invertible_of_stackedNormalEquations
        (Za := Za) (Zb := Zb) (X := X)
        hZa hZ hR hFitted hMaintainedMoment)
      hunit
      (TwoSLSSubsetResidualizedGaussianCriterionInputs.of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (A := A)
        hFull.toJointIidMixedMomentConditions β hMaintained.model
        hZa hZ hA hcov hR_rowGram)

set_option linter.style.longLine false in
/-- Textbook-fourth full-Gram and fitted-Gram facade with the limiting
covariance regularity stated directly on Hansen's displayed residualized-score
target.

This removes the separate limiting row-Gram certificate from the strongest
Theorem 12.17 condition constructor.  The caller proves positive definiteness
of `(A M) Ω (A M)'`, while this constructor still derives the residualized
instrument Gram and both 2SLS moment branches from finite-sample Gram
certificates. -/
theorem
    of_normalEquations_fullResidualScoreMap_covarianceTarget_posDef_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hV_pos :
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A).PosDef) :
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df := by
  let hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      residualizedInstrumentsGram_invertible_of_fromCols_gram_invertible
        (stackRegressors Za m ω) (stackRegressors Zb m ω) (hZ m ω)
  let hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      twoSLSMomentMatrixStar_invertible_of_fittedRegressorsStar_gram_invertible
        (stackRegressors Za m ω) (stackRegressors X m ω)
        (hMaintainedFitted m ω)
  let hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det := by
    intro m ω
    classical
    rcases hZ m ω with ⟨instZ⟩
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
      instZ
    exact
      twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible
        (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (stackRegressors X m ω) (hFitted m ω)
  exact
    of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (V := twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A)
      hover hdf hMaintained.toJointIidMixedMomentConditions
      hFull.toJointIidMixedMomentConditions β hMaintained.model hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment
      (twoSLSSubsetDualSchurComplement_invertible_of_stackedNormalEquations
        (Za := Za) (Zb := Zb) (X := X)
        hZa hZ hR hFitted hMaintainedMoment)
      hunit
      (TwoSLSSubsetResidualizedGaussianCriterionInputs.of_assumption12_2_fullResidualScoreMap
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (A := A)
        hFull.toJointIidMixedMomentConditions β hMaintained.model
        hZa hZ hA hV hV_pos
        (by
          simp [twoSLSSubsetResidualizedScoreCovariance, Matrix.transpose_mul,
            Matrix.mul_assoc]))

end TwoSLSSubsetCommonSigmaSlutskyBridgeConditions

/-- The Slutsky common-denominator bridge derives the ordinary Sargan-difference
chi-square limit. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.sarganDiffLimit
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  have hdiff :
      TendstoInMeasure μ
        ((fun (m : ℕ) ω =>
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) -
        (fun (m : ℕ) ω =>
          twoSLSSubsetSarganDiffCommonSigmaStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)))
        atTop (fun _ => 0) := by
    simpa [Pi.sub_apply, sub_eq_add_neg, add_comm] using
      TendstoInMeasure.neg_zero_real
        h.common_minus_sargan_diff_tendstoInMeasure_zero
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (m : ℕ) ω =>
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (Y := fun (m : ℕ) ω =>
      twoSLSSubsetSarganDiffStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (Z := fun x : ℝ => x)
    h.common_limit hdiff h.sargan_diff_aemeasurable

/-- The Slutsky common-denominator bridge gives the Newey statistic
chi-square limit from the exact identity `N = C*`. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.neweyLimit
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl h.common_limit
  intro m
  exact ae_of_all μ (fun ω => (h.newey_eq_common m ω).symm)

/-- Exact `N - C* = 0` consequence of the subset-overidentification algebraic
identity, stated as convergence in measure for composition with Slutsky
arguments. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.neweyMinusCommon_tendstoInMeasure_zero
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) := by
  have hzero :
      TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hzero
  intro m
  exact ae_of_all μ (fun ω => by
    change (0 : ℝ) =
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) -
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)
    rw [h.newey_eq_common m ω, sub_self])

/-- Convert the Slutsky common-denominator package into the older exact
common-sigma bridge by deriving the ordinary Sargan-difference chi-square limit
from `C* ⇒ χ²` and `C* - C = oₚ(1)`. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.toCommonSigmaBridgeConditions
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TwoSLSSubsetCommonSigmaBridgeConditions μ Za Zb X Y df where
  maintained_overidentified := h.maintained_overidentified
  df_eq := h.df_eq
  newey_eq_common := h.newey_eq_common
  common_limit := h.common_limit
  sargan_diff_limit := h.sarganDiffLimit
  common_minus_sargan_diff_tendstoInMeasure_zero :=
    h.common_minus_sargan_diff_tendstoInMeasure_zero

/-- Convert the exact common-denominator bridge package into the theorem-facing
subset-overidentification condition package. -/
theorem TwoSLSSubsetCommonSigmaBridgeConditions.toSubsetOveridConditions
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaBridgeConditions μ Za Zb X Y df) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df where
  maintained_overidentified := h.maintained_overidentified
  df_eq := h.df_eq
  newey_eq_common := h.newey_eq_common
  newey_limit := by
    refine TendstoInDistribution.congr ?_ EventuallyEq.rfl h.common_limit
    intro m
    exact ae_of_all μ (fun ω => (h.newey_eq_common m ω).symm)
  sargan_diff_limit := h.sargan_diff_limit
  asymptotic_equivalence := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl
      h.common_minus_sargan_diff_tendstoInMeasure_zero
    intro m
    exact ae_of_all μ (fun ω =>
      congrArg
        (fun t => t -
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
        (h.newey_eq_common m ω).symm)

/-- Convert the Slutsky common-denominator bridge package into the
theorem-facing subset-overidentification condition package. -/
theorem TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.toSubsetOveridConditions
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df where
  maintained_overidentified := h.maintained_overidentified
  df_eq := h.df_eq
  newey_eq_common := h.newey_eq_common
  newey_limit := by
    refine TendstoInDistribution.congr ?_ EventuallyEq.rfl h.common_limit
    intro m
    exact ae_of_all μ (fun ω => (h.newey_eq_common m ω).symm)
  sargan_diff_limit := h.sarganDiffLimit
  asymptotic_equivalence := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl
      h.common_minus_sargan_diff_tendstoInMeasure_zero
    intro m
    exact ae_of_all μ (fun ω =>
      congrArg
        (fun t => t -
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
        (h.newey_eq_common m ω).symm)

/-- Hansen Theorem 12.17 deterministic identity `N = C*`. -/
theorem twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y df) :
    ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) :=
  h.newey_eq_common

/-- Hansen Theorem 12.17: Newey's subset-overidentification statistic has the
`χ²_{ℓ_b}` null limit in the textbook-cardinality specialization. -/
theorem twoSLSSubsetNeweyStatOrZero_tendstoInDistribution_chiSquared_card
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb)) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) :=
  h.newey_limit

/-- Hansen Theorem 12.17: the Sargan-difference subset statistic has the
`χ²_{ℓ_b}` null limit in the textbook-cardinality specialization. -/
theorem twoSLSSubsetSarganDiffStatOrZero_tendstoInDistribution_chiSquared_card
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb)) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) :=
  h.sargan_diff_limit

/-- Hansen Theorem 12.17 Newey statistic endpoint from the Slutsky
common-denominator bridge.  This derives `N ⇒ χ²` from `N = C*` and the
common-denominator limit. -/
theorem twoSLSSubsetNeweyStatOrZero_tendstoInDistribution_chiSquared_of_commonSigmaSlutskyBridge
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  h.neweyLimit

/-- Hansen Theorem 12.17 ordinary Sargan-difference endpoint from the Slutsky
common-denominator bridge.  This derives `C ⇒ χ²` from `C* ⇒ χ²` and
`C* - C = oₚ(1)`. -/
theorem
    twoSLSSubsetSarganDiffStatOrZero_tendstoInDistribution_chiSquared_of_commonSigmaSlutskyBridge
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
  h.sarganDiffLimit

/-- Exact `N - C* = 0` endpoint from the Slutsky common-denominator bridge. -/
theorem
    twoSLSSubsetNeweyStatOrZero_sub_commonSigma_tendstoInMeasure_zero_of_commonSigmaSlutskyBridge
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) :=
  h.neweyMinusCommon_tendstoInMeasure_zero

/-- The assumed `C* - C = oₚ(1)` field of the Slutsky bridge, exposed as a
citeable endpoint with the chapter statistic names. -/
theorem twoSLSSubsetCommonSigmaStatOrZero_sub_sarganDiff_tendstoInMeasure_zero_of_commonSigmaSlutskyBridge
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) :=
  h.common_minus_sargan_diff_tendstoInMeasure_zero

/-- Hansen Theorem 12.17: Newey's statistic and the Sargan-difference statistic
are asymptotically equivalent. -/
theorem twoSLSSubsetNeweyStatOrZero_sub_sarganDiff_tendstoInMeasure_zero
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y df) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) :=
  h.asymptotic_equivalence

/-- Hansen Theorem 12.17 calibrated-size wrapper for Newey's subset statistic
with the textbook `χ²_{ℓ_b}` critical value. -/
theorem twoSLSSubsetNeweyTest_rejectionProb_tendsto_alpha_card
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ)
    (W := fun m ω =>
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (q := Fintype.card lb) (crit := crit) (alpha := alpha) hcrit
    h.newey_limit

/-- Hansen Theorem 12.17 calibrated-size wrapper for the Sargan-difference
subset statistic with the textbook `χ²_{ℓ_b}` critical value. -/
theorem twoSLSSubsetSarganDiffTest_rejectionProb_tendsto_alpha_card
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
    (μ := μ)
    (W := fun m ω =>
      twoSLSSubsetSarganDiffStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω))
    (q := Fintype.card lb) (crit := crit) (alpha := alpha) hcrit
    h.sargan_diff_limit

/-- Lower-tail critical-value convention for Newey's subset-overidentification
test with textbook degrees of freedom `ℓ_b`. -/
theorem twoSLSSubsetNeweyTest_rejectionProb_tendsto_alpha_card_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Iic crit) = 1 - alpha) :
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetNeweyTest_rejectionProb_tendsto_alpha_card h
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card lb) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Lower-tail critical-value convention for the Sargan-difference subset test
with textbook degrees of freedom `ℓ_b`. -/
theorem twoSLSSubsetSarganDiffTest_rejectionProb_tendsto_alpha_card_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Iic crit) = 1 - alpha) :
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetSarganDiffTest_rejectionProb_tendsto_alpha_card h
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card lb) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Hansen Theorem 12.17 rejection-probability equivalence for Newey's subset
test and the Sargan-difference subset test.

Both rejection probabilities converge to the same calibrated upper-tail
probability, so their truncated differences vanish in both directions.  This is
the probability-level form of the asymptotic equivalence statement, complementing
`twoSLSSubsetNeweyStatOrZero_sub_sarganDiff_tendstoInMeasure_zero`. -/
theorem twoSLSSubsetNeweySarganDiffTest_rejectionProb_equiv_card
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun m =>
        μ {ω | crit <
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)} -
        μ {ω | crit <
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) ∧
    Tendsto
      (fun m =>
        μ {ω | crit <
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)} -
        μ {ω | crit <
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) := by
  have hNewey :=
    twoSLSSubsetNeweyTest_rejectionProb_tendsto_alpha_card
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y) h hcrit
  have hSargan :=
    twoSLSSubsetSarganDiffTest_rejectionProb_tendsto_alpha_card
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y) h hcrit
  have halpha_ne_top : alpha ≠ ∞ := by
    rw [← hcrit]
    exact measure_ne_top (chiSquared (Fintype.card lb)) (Set.Ioi crit)
  refine ⟨?_, ?_⟩
  · simpa using ENNReal.Tendsto.sub hNewey hSargan (Or.inl halpha_ne_top)
  · simpa using ENNReal.Tendsto.sub hSargan hNewey (Or.inl halpha_ne_top)

/-- Lower-tail critical-value convention for
`twoSLSSubsetNeweySarganDiffTest_rejectionProb_equiv_card`. -/
theorem twoSLSSubsetNeweySarganDiffTest_rejectionProb_equiv_card_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Iic crit) = 1 - alpha) :
    Tendsto
      (fun m =>
        μ {ω | crit <
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)} -
        μ {ω | crit <
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) ∧
    Tendsto
      (fun m =>
        μ {ω | crit <
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)} -
        μ {ω | crit <
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) :=
  twoSLSSubsetNeweySarganDiffTest_rejectionProb_equiv_card h
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card lb) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Hansen Theorem 12.17: `N = C*`, both subset-overidentification statistics
have `χ²_{ℓ_b}` null limits, and the rejection rules have calibrated asymptotic
size. -/
theorem twoSLSSubsetOverid_theorem12_17
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y df)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  have hNsize :
      Tendsto
        (fun m => μ {ω | crit <
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)})
        atTop (𝓝 alpha) :=
    chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
      (μ := μ)
      (W := fun m ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (q := df) (crit := crit) (alpha := alpha) hcrit h.newey_limit
  have hCsize :
      Tendsto
        (fun m => μ {ω | crit <
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)})
        atTop (𝓝 alpha) :=
    chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
      (μ := μ)
      (W := fun m ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (q := df) (crit := crit) (alpha := alpha) hcrit h.sargan_diff_limit
  exact ⟨h.newey_eq_common, h.newey_limit, h.sargan_diff_limit,
    h.asymptotic_equivalence, hNsize, hCsize⟩

/-- Hansen Theorem 12.17 lower-tail critical-value convention. -/
theorem twoSLSSubsetOverid_theorem12_17_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y df)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17 h
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := df) (c := crit) (alpha := alpha) halpha_le_one hcrit)

/-- Hansen Theorem 12.17 with the textbook degrees of freedom fixed directly
as the excluded-instrument block size `ℓ_b`. -/
theorem twoSLSSubsetOverid_theorem12_17_card
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17 h hcrit

/-- Hansen Theorem 12.17 lower-tail critical-value convention with the
textbook excluded-instrument block size `ℓ_b`. -/
theorem twoSLSSubsetOverid_theorem12_17_card_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetOveridConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_card h
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := Fintype.card lb) (c := crit) (alpha := alpha)
      halpha_le_one hcrit)

/-- Hansen Theorem 12.17 from the exact common-denominator bridge package. -/
theorem twoSLSSubsetOverid_theorem12_17_of_commonSigmaBridge
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaBridgeConditions μ Za Zb X Y df)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17 h.toSubsetOveridConditions hcrit

/-- Hansen Theorem 12.17 lower-tail critical-value convention from the exact
common-denominator bridge package. -/
theorem twoSLSSubsetOverid_theorem12_17_of_commonSigmaBridge_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaBridgeConditions μ Za Zb X Y df)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail h.toSubsetOveridConditions
    halpha_le_one hcrit

/-- Hansen Theorem 12.17, textbook-degree form, from the exact
common-denominator bridge package. -/
theorem twoSLSSubsetOverid_theorem12_17_card_of_commonSigmaBridge
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetCommonSigmaBridgeConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_card h.toSubsetOveridConditions hcrit

/-- Hansen Theorem 12.17, textbook-degree lower-tail form, from the exact
common-denominator bridge package. -/
theorem twoSLSSubsetOverid_theorem12_17_card_of_commonSigmaBridge_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetCommonSigmaBridgeConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_card_lowerTail h.toSubsetOveridConditions
    halpha_le_one hcrit

/-- Hansen Theorem 12.17 from the Slutsky common-denominator bridge package.

This version derives the ordinary Sargan-difference chi-square limit from the
common-denominator limit and `C* - C = o_p(1)`. -/
theorem twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17 h.toSubsetOveridConditions hcrit

/-- Hansen Theorem 12.17 lower-tail critical-value convention from the Slutsky
common-denominator bridge package. -/
theorem twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y df)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail h.toSubsetOveridConditions
    halpha_le_one hcrit

/-- Hansen Theorem 12.17, textbook-degree form, from the Slutsky
common-denominator bridge package. -/
theorem twoSLSSubsetOverid_theorem12_17_card_of_commonSigmaSlutskyBridge
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_card h.toSubsetOveridConditions hcrit

/-- Hansen Theorem 12.17, textbook-degree lower-tail form, from the Slutsky
common-denominator bridge package. -/
theorem twoSLSSubsetOverid_theorem12_17_card_of_commonSigmaSlutskyBridge_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    (h : TwoSLSSubsetCommonSigmaSlutskyBridgeConditions μ Za Zb X Y (Fintype.card lb))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared (Fintype.card lb)) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_card_lowerTail h.toSubsetOveridConditions
    halpha_le_one hcrit

/-- Hansen Theorem 12.17 directly from the normal-equation proof of
`N = C*` and a Chapter 9 criterion proof of the common-denominator
chi-square limit. -/
theorem twoSLSSubsetOverid_theorem12_17_of_normalEquations_commonCriterion
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → Ω → lb → ℝ} {G : Ωlim → lb → ℝ}
    {Vhat : ℕ → Ω → Matrix lb lb ℝ} {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hstat : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      criterionJStatOrZero (T m ω) (Vhat m ω))
    (hT : TendstoInDistribution T atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable (Vhat m) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν)
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_commonCriterion
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (T := T) (G := G) (Vhat := Vhat) (V := V)
      hover hdf hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hstat hT hV_meas hV hV_nonsing hLaw haemeas hdiff)
    hcrit

/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_commonCriterion`. -/
theorem twoSLSSubsetOverid_theorem12_17_of_normalEquations_commonCriterion_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → Ω → lb → ℝ} {G : Ωlim → lb → ℝ}
    {Vhat : ℕ → Ω → Matrix lb lb ℝ} {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hstat : ∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      criterionJStatOrZero (T m ω) (Vhat m ω))
    (hT : TendstoInDistribution T atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable (Vhat m) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν)
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge_lowerTail
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_commonCriterion
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (T := T) (G := G) (Vhat := Vhat) (V := V)
      hover hdf hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hstat hT hV_meas hV hV_nonsing hLaw haemeas hdiff)
    halpha_le_one hcrit

/-- Hansen Theorem 12.17 directly from the normal-equation proof of
`N = C*` and the concrete residualized-score criterion statistic.

This is the theorem-facing version of
`TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreCriterion`:
callers supply the residualized subset-score CLT, covariance consistency, the
limiting quadratic-form law, and `C* - C = o_p(1)`, but no longer supply a
separate statistic-identification equality. -/
theorem twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedScoreCriterion
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {G : Ωlim → lb → ℝ} {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν)
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreCriterion
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (G := G) (V := V)
      hover hdf hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV_meas hV hV_nonsing hLaw haemeas hdiff)
    hcrit

/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedScoreCriterion`. -/
theorem twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedScoreCriterion_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {G : Ωlim → lb → ℝ} {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop G (fun _ => μ) ν)
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun ω => G ω ⬝ᵥ (V⁻¹ *ᵥ G ω)) (chiSquared df) ν)
    (haemeas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge_lowerTail
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreCriterion
      (μ := μ) (ν := ν) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (G := G) (V := V)
      hover hdf hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV_meas hV hV_nonsing hLaw haemeas hdiff)
    halpha_le_one hcrit

/-- Hansen Theorem 12.17 from normal equations and a residualized-score
Gaussian criterion route.

Compared with
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedScoreCriterion`,
this wrapper derives the limiting `χ²_{ℓ_b}` law internally from a
positive-definite Gaussian subset-score limit, and derives ordinary
Sargan-difference measurability from row measurability. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedScoreGaussianCriterion_of_rows
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreGaussianCriterion_of_rows
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      hover hdf hZa_meas hZb_meas hX_meas hY_meas
      hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV_meas hV hV_pos hdiff)
    hcrit

/-- Lower-tail critical-value convention for the Gaussian residualized-score
route in Hansen Theorem 12.17. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedScoreGaussianCriterion_of_rows_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ)
    (hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    (hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge_lowerTail
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreGaussianCriterion_of_rows
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      hover hdf hZa_meas hZb_meas hX_meas hY_meas
      hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV_meas hV hV_pos hdiff)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 from primitive mixed-moment Assumption 12.2 packages,
conditional homoskedasticity, normal equations, and a Gaussian residualized
subset-score CLT.

This theorem-facing wrapper composes the homoskedastic denominator-replacement
constructor with the existing Slutsky theorem.  It derives ordinary
Sargan-difference measurability, maintained-numerator tightness, and
`C* - C = o_p(1)` internally; the residualized subset-score CLT, Newey
covariance consistency/positive-definiteness, and finite-sample normal-equation
branches remain the explicit primitive inputs. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_homoskedastic
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_homoskedastic
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (V := V) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV hV_pos)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for the primitive homoskedastic
Assumption-12.2 route in Hansen Theorem 12.17. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_homoskedastic_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hT : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) =>
        (Real.sqrt (m : ℝ))⁻¹ •
          twoSLSSubsetResidualizedScoreStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun z : EuclideanSpace ℝ lb => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 V))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => V))
    (hV_pos : V.PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge_lowerTail
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedScoreGaussianCriterion_assumption12_2_homoskedastic
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (V := V) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hT hV hV_pos)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 from primitive mixed-moment Assumption 12.2 packages,
conditional homoskedasticity, normal equations, and the packaged Gaussian
residualized subset-score criterion inputs. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hGaussian :
      TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y V)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (V := V) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hGaussian)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for the packaged Gaussian criterion
route in Hansen Theorem 12.17. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {V : Matrix lb lb ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hGaussian :
      TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y V)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge_lowerTail
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_residualizedGaussianCriterionInputs_assumption12_2_homoskedastic
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (V := V) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hGaussian)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 from Assumption 12.2, homoskedasticity, normal
equations, and the canonical displayed residualized covariance target.

This theorem-facing wrapper derives the residualized Gaussian criterion package
from the full residual-score CLT and the full-row-rank displayed covariance
route, then reuses the packaged homoskedastic normal-equations theorem. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M)))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hA hV hR_fullRowRank)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hSchur : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω) -
          (twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
            fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω) *
            (((fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
              fittedRegressorsStar
                (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
                (stackRegressors X m ω))⁻¹) *
            (fittedRegressorsStar
              (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
              (stackRegressors X m ω))ᵀ *
            twoSLSSubsetResidualizedInstrumentsStar
              (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M)))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge_lowerTail
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hSchur hunit
      hA hV hR_fullRowRank)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 from Assumption 12.2, homoskedasticity, normal
equations, and the canonical displayed residualized covariance target, with the
dual Newey Schur branch derived internally.

Compared with
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic`,
this theorem-facing wrapper no longer asks for the dual Schur nonsingularity
premise.  It derives that branch from the maintained/full instrument Gram,
residualized-instrument Gram, full fitted-regressor Gram, and maintained moment
branches via the finite-sample normal-equation bridge. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M)))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hunit
      hA hV hR_fullRowRank)
    hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 upper-tail endpoint using the canonical population-Gram
score-map limit.

This removes the explicit residualized score-map convergence premise from the
derived-dual-Schur route: the limiting map is
`twoSLSSubsetResidualizedScoreMapFromGram (popGram μ [Z_a,Z_b])`, and its
sample convergence is derived from the full-instrument Assumption 12.2
sample-Gram WLLN. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_rowGram : IsUnit
      (let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      hover hdf hMaintained hFull β hmodel hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hunit hV hR_rowGram)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e)
    (hFull : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M)))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_commonSigmaSlutskyBridge_lowerTail
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull β hmodel hZa0 hhomo
      hsigma_pos hZa hZ hR hFitted hMaintainedMoment hunit
      hA hV hR_fullRowRank)
    halpha_le_one hcrit

/-- Hansen Theorem 12.17 condition package from literal Assumption 12.2
fourth-moment hypotheses.

This is the textbook-facing facade over the tightened homoskedastic route:
the maintained numerator tightness, full residual-score CLT transport,
covariance positive-definiteness, denominator replacement, ordinary
Sargan-difference measurability, and dual Schur branch are all derived by the
existing Chapter 12.2/12.3 surfaces and finite-sample normal-equation algebra.
The remaining explicit inputs are the subset-specific residualized score-map
convergence, Newey covariance consistency to the displayed target, finite
sample nonsingularity branches, and full row rank of the limiting
residualized-score map. -/
theorem TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M))) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df :=
  TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.toSubsetOveridConditions
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hunit hA hV hR_fullRowRank)

set_option linter.style.longLine false in
/-- Textbook-facing Theorem 12.17 condition package from literal Assumption
12.2 fourth-moment hypotheses and the nonsingular limiting residualized-score
row Gram.

This is the same tightened homoskedastic route as
`TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur`,
but exposes the row-Gram rank certificate directly. -/
theorem
    TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df :=
  TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
    hZa hZ hR hFitted hMaintainedMoment hunit hA hV
    (twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
      μ Za Zb X A hR_rowGram)

set_option linter.style.longLine false in
/-- Textbook-facing Theorem 12.17 condition package with the full 2SLS
moment determinant branch derived from the full fitted-regressor Gram.

This removes the redundant finite-sample `hunit` premise from the row-Gram
facade: on the nonsingular full-instrument branch, `Xhat'Xhat = X'P_Z X`, so
`hFitted` already supplies the determinant certificate used by the Star
normal-equation identities. -/
theorem
    TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fittedGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df := by
  let hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det := by
    intro m ω
    classical
    rcases hZ m ω with ⟨instZ⟩
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
      instZ
    exact
      twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible
        (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (stackRegressors X m ω) (hFitted m ω)
  exact
    TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hunit hA hV hR_rowGram

set_option linter.style.longLine false in
/-- Textbook-facing Theorem 12.17 condition package with both finite-sample
residualized-instrument and full 2SLS moment branches derived from Gram
certificates.

The residualized-instrument Gram is obtained as the Schur complement of the
maintained-instrument block inside `[Z_a,Z_b]'[Z_a,Z_b]`; the full 2SLS moment
determinant branch is obtained from the fitted-regressor Gram. -/
theorem
    TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df := by
  let hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      residualizedInstrumentsGram_invertible_of_fromCols_gram_invertible
        (stackRegressors Za m ω) (stackRegressors Zb m ω) (hZ m ω)
  exact
    TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fittedGram
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hA hV hR_rowGram

set_option linter.style.longLine false in
/-- Textbook-facing Theorem 12.17 condition package with finite-sample
residualized-instrument, full 2SLS moment, and maintained 2SLS moment branches
derived from Gram certificates.

Compared with
`TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGram`,
this facade also derives the maintained-model 2SLS moment branch from the
maintained fitted-regressor Gram. -/
theorem
    TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df :=
  TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.toSubsetOveridConditions
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedFitted hA hV hR_rowGram)

set_option linter.style.longLine false in
/-- Textbook-facing Theorem 12.17 condition package with the residualized
score-map limit derived from the full-instrument sample-Gram WLLN.

This is the full-Gram/fitted-Grams facade with Hansen's literal finite-fourth
Assumption 12.2 package at the boundary.  It fixes the limiting residualized
score map to `twoSLSSubsetResidualizedScoreMapFromGram (popGram μ [Z_a,Z_b])`
and reuses the mixed-moment full-instrument sample-Gram constructor internally,
while retaining the finite-sample Gram certificates used by the strongest
abstract-`A` facade. -/
theorem
    TwoSLSSubsetOveridConditions.of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_rowGram : IsUnit
      (let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df := by
  let hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      residualizedInstrumentsGram_invertible_of_fromCols_gram_invertible
        (stackRegressors Za m ω) (stackRegressors Zb m ω) (hZ m ω)
  let hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))) := by
    intro m ω
    classical
    rcases hZa m ω with ⟨instZa⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) := instZa
    exact
      twoSLSMomentMatrixStar_invertible_of_fittedRegressorsStar_gram_invertible
        (stackRegressors Za m ω) (stackRegressors X m ω)
        (hMaintainedFitted m ω)
  let hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det := by
    intro m ω
    classical
    rcases hZ m ω with ⟨instZ⟩
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
      instZ
    exact
      twoSLSMomentMatrixStar_det_isUnit_of_fittedRegressorsStar_gram_invertible
        (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (stackRegressors X m ω) (hFitted m ω)
  exact
    TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.toSubsetOveridConditions
      (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_homoskedastic_derivedDualSchur
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        hover hdf hMaintained.toJointIidMixedMomentConditions
        hFull.toJointIidMixedMomentConditions β hMaintained.model hZa0
        hhomo hsigma_pos hZa hZ hR hFitted hMaintainedMoment hunit hV
        hR_rowGram)

set_option linter.style.longLine false in
/-- Textbook-facing Theorem 12.17 condition package with Newey covariance
consistency derived from the full-instrument covariance identity.

This is the condition-package counterpart of the row-Gram full-Gram/fitted-Gram
facade, but replaces the primitive covariance convergence premise by
`scoreCovMat μ [Za,Zb] e = σ² QZZ`. -/
theorem
    TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det) :
    TwoSLSSubsetOveridConditions μ Za Zb X Y df :=
  TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.toSubsetOveridConditions
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedFitted hA hcov hR_rowGram)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 from literal finite-fourth Assumption 12.2 packages,
conditional homoskedasticity, finite-sample normal-equation branches, and the
displayed residualized-score covariance target.

This is a theorem-facing wrapper over
`TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur`.
It keeps the remaining subset-specific stochastic inputs explicit: convergence
of the residualized score map, Newey covariance consistency to the displayed
target, and full row rank of the limiting residualized-score map. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M)))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hunit hA hV hR_fullRowRank)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_fullRowRank :
      let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X))
      let QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Zfull X))
      let M := twoSLSOveridPopulationResidualMaker QXZ QZZ QZX
      Function.Injective (fun v : lb → ℝ => Matrix.vecMul v (A * M)))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hunit hA hV hR_fullRowRank)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 from literal finite-fourth Assumption 12.2 packages,
with the limiting residualized-score full-rank input supplied as a nonsingular
row-Gram certificate. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hunit hA hV hR_rowGram)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hunit : ∀ (m : ℕ) (ω : Ω),
      IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det)
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hunit hA hV hR_rowGram)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 from literal finite-fourth Assumption 12.2 packages,
with the limiting row-Gram certificate and the full 2SLS moment determinant
branch derived from the full fitted-regressor Gram. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fittedGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fittedGram
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hA hV hR_rowGram)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fittedGram`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fittedGram_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hR : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          twoSLSSubsetResidualizedInstrumentsStar
            (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fittedGram
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hR hFitted hMaintainedMoment hA hV hR_rowGram)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 with the finite-sample residualized-instrument Gram
derived from the maintained/full instrument Grams by Schur complement, and the
full 2SLS moment branch derived from the fitted-regressor Gram. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGram
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGram
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedMoment hA hV hR_rowGram)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGram`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGram_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedMoment : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGram
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedMoment hA hV hR_rowGram)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 with the finite-sample residualized-instrument Gram
and both 2SLS moment branches derived from Gram certificates.

The maintained and full instrument Grams give the residualized excluded
instrument Gram by Schur complement.  The maintained and full fitted-regressor
Grams give the corresponding 2SLS moment matrix branches, so the caller no
longer supplies maintained moment nonsingularity directly. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedFitted hA hV hR_rowGram)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail
      (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedFitted hA hV hR_rowGram)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 with the residualized score-map limit derived from
the full-instrument sample-Gram WLLN.

This is the full-Gram/fitted-Grams, literal finite-fourth facade for the
upper-tail critical-value convention.  It fixes the residualized score-map
target to Hansen's population-Gram formula and removes the separate `hA`
premise from the strongest covariance-target endpoint. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_rowGram : IsUnit
      (let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      hover hdf hMaintained hFull hZa0 hhomo hsigma_pos hZa hZ
      hFitted hMaintainedFitted hV hR_rowGram)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_rowGram : IsUnit
      (let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      hover hdf hMaintained hFull hZa0 hhomo hsigma_pos hZa hZ
      hFitted hMaintainedFitted hV hR_rowGram)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Observed-row facade for Hansen Theorem 12.17 with the residualized
score-map limit derived from the full-instrument sample-Gram WLLN.

This is the upper-tail critical-value convention.  The maintained and full
instrument Assumption 12.2 packages are stated on Hansen's observed rows and
converted to the residual-row proof engine at the boundary. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_rowGram : IsUnit
      (let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    hover hdf hMaintained.toResidualTextbookFourthConditions
    hFull.toResidualTextbookFourthConditions hZa0 hhomo hsigma_pos hZa hZ
    hFitted hMaintainedFitted hV hR_rowGram hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ =>
          twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e
            (twoSLSSubsetResidualizedScoreMapFromGram
              (popGram μ (fun i ω => Sum.elim (Za i ω) (Zb i ω))))))
    (hR_rowGram : IsUnit
      (let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
        fun i ω => Sum.elim (Za i ω) (Zb i ω)
      let A : Matrix lb (la ⊕ lb) ℝ :=
        twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
      (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det))
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    hover hdf hMaintained.toResidualTextbookFourthConditions
    hFull.toResidualTextbookFourthConditions hZa0 hhomo hsigma_pos hZa hZ
    hFitted hMaintainedFitted hV hR_rowGram halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 with Newey covariance consistency derived from
full-instrument sample moments and the full-instrument covariance identity.

This is the row-Gram full-Gram/fitted-Gram facade for the upper-tail critical
value convention.  It keeps Hansen's literal finite-fourth Assumption 12.2
packages at the boundary, derives the finite-sample residualized and moment
branches from Gram certificates, and replaces the primitive covariance
convergence premise by `scoreCovMat μ [Za,Zb] e = σ² QZZ`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedFitted hA hcov hR_rowGram)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail
    (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedFitted hA hcov hR_rowGram)
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Hansen Theorem 12.17 with the Newey covariance target derived from
full-instrument homoskedasticity.

The full-instrument homoskedasticity premise supplies both the maintained-block
homoskedasticity used for the common-denominator replacement `C* - C = o_p(1)`
and the covariance identity `scoreCovMat μ [Za,Zb] e = σ² QZZ` through the
reusable Chapter 7/12 bridges. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  have hhomo : HomoskedasticErrorVariance μ Za e :=
    HomoskedasticErrorVariance.of_twoSLSCombined_left
      (μ := μ) (Za := Za) (Zb := Zb) (e := e) hZfull0 hhomoFull
  have hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)) :=
    scoreCovMat_eq_errorVariance_smul_twoSLSCombinedQZZ_of_assumption12_2_homoskedastic
      (μ := μ) (Z := fun i ω => Sum.elim (Za i ω) (Zb i ω))
      (X := X) (e := e)
      hFull.toJointIidMixedMomentConditions hZfull0 hhomoFull
  exact
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedFitted hA hcov hR_rowGram hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  have hhomo : HomoskedasticErrorVariance μ Za e :=
    HomoskedasticErrorVariance.of_twoSLSCombined_left
      (μ := μ) (Za := Za) (Zb := Zb) (e := e) hZfull0 hhomoFull
  have hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)) :=
    scoreCovMat_eq_errorVariance_smul_twoSLSCombinedQZZ_of_assumption12_2_homoskedastic
      (μ := μ) (Z := fun i ω => Sum.elim (Za i ω) (Zb i ω))
      (X := X) (e := e)
      hFull.toJointIidMixedMomentConditions hZfull0 hhomoFull
  exact
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
      hZa hZ hFitted hMaintainedFitted hA hcov hR_rowGram
      halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Observed-row facade for Hansen Theorem 12.17 with the Newey covariance
target derived from full-instrument homoskedasticity.

The maintained and full Assumption 12.2 packages are stated on Hansen's
observed rows and converted to the residual-row proof engine at the boundary.
This keeps the theorem-facing API aligned with the textbook rows while reusing
the full-homoskedastic Newey covariance route. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) hover hdf hMaintained.toResidualTextbookFourthConditions
    hFull.toResidualTextbookFourthConditions hZa0 hZfull0 hhomoFull
    hsigma_pos hZa hZ hFitted hMaintainedFitted hA hR_rowGram hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) hover hdf hMaintained.toResidualTextbookFourthConditions
    hFull.toResidualTextbookFourthConditions hZa0 hZfull0 hhomoFull
    hsigma_pos hZa hZ hFitted hMaintainedFitted hA hR_rowGram
    halpha_le_one hcrit

set_option linter.style.longLine false in
/-- Observed-row Hansen Theorem 12.17 full-homoskedastic facade with scalar
variance positivity derived from the full-instrument Assumption 12.2 package. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  have hfull_card : 0 < Fintype.card (la ⊕ lb) - Fintype.card k := by
    rw [tsub_pos_iff_lt, Fintype.card_sum]
    exact lt_of_lt_of_le hover (Nat.le_add_right _ _)
  letI : Fact (0 < Fintype.card (la ⊕ lb) - Fintype.card k) := ⟨hfull_card⟩
  have hsigma_pos : 0 < errorVariance μ e :=
    errorVariance_pos_of_assumption12_2_observed_textbook_fourth_homoskedastic
      (μ := μ) (Z := fun i ω => Sum.elim (Za i ω) (Zb i ω))
      (X := X) (e := e) (Y := Y) (β := β)
      hFull hZfull0 hhomoFull
  exact
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      (A := A) hover hdf hMaintained hFull hZa0 hZfull0 hhomoFull
      hsigma_pos hZa hZ hFitted hMaintainedFitted hA hR_rowGram hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    (A := A) hover hdf hMaintained hFull hZa0 hZfull0 hhomoFull
    hZa hZ hFitted hMaintainedFitted hA hR_rowGram
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := df) (c := crit) (alpha := alpha) halpha_le_one hcrit)

set_option linter.style.longLine false in
/-- Observed-row Hansen Theorem 12.17 facade deriving the residualized score-map
limit from the full-instrument sample-Gram WLLN and deriving scalar variance
positivity from full-instrument homoskedasticity.

The limiting residualized score map is fixed to Hansen's population
full-instrument Gram expression, and the Newey covariance target is derived
from full-instrument homoskedasticity.  Finite-sample identities are used on
rank events whose complements have vanishing probability.  The shorter
`Theorem12_17.observed` wrapper derives those rank probabilities and limiting
row-Gram nonsingularity from observed Assumption 12.2. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hrank : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun m => μ {ω |
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) ≠
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) := by
  let Zfull : ℕ → Ω → (la ⊕ lb) → ℝ :=
    fun i ω => Sum.elim (Za i ω) (Zb i ω)
  let A : Matrix lb (la ⊕ lb) ℝ :=
    twoSLSSubsetResidualizedScoreMapFromGram (popGram μ Zfull)
  have hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A) := by
    simpa [A, Zfull] using
      TwoSLSSubsetResidualizedGaussianCriterionInputs.twoSLSSubsetResidualizedScoreMapStar_tendstoInMeasure_of_assumption12_2_fullInstrumentSampleGram
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e)
        hMaintained.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
        hFull.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
  let hMaintainedMixed :
      TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Za X e :=
    hMaintained.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
  let hFullMixed : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      μ Zfull X e := by
    simpa [Zfull] using
      hFull.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
  have hfull_card : 0 < Fintype.card (la ⊕ lb) - Fintype.card k := by
    rw [tsub_pos_iff_lt, Fintype.card_sum]
    exact lt_of_lt_of_le hover (Nat.le_add_right _ _)
  letI : Fact (0 < Fintype.card (la ⊕ lb) - Fintype.card k) := ⟨hfull_card⟩
  have hhomo : HomoskedasticErrorVariance μ Za e :=
    HomoskedasticErrorVariance.of_twoSLSCombined_left
      (μ := μ) (Za := Za) (Zb := Zb) (e := e) hZfull0 hhomoFull
  have hsigma_pos : 0 < errorVariance μ e :=
    errorVariance_pos_of_assumption12_2_observed_textbook_fourth_homoskedastic
      (μ := μ) (Z := Zfull) (X := X) (e := e) (Y := Y) (β := β)
      (by simpa [Zfull] using hFull) hZfull0 (by simpa [Zfull] using hhomoFull)
  have hcov :
      scoreCovMat μ Zfull e =
        errorVariance μ e •
          twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Zfull X)) := by
    simpa [Zfull] using
      scoreCovMat_eq_errorVariance_smul_twoSLSCombinedQZZ_of_assumption12_2_homoskedastic
        (μ := μ) (Z := fun i ω => Sum.elim (Za i ω) (Zb i ω))
        (X := X) (e := e)
        hFull.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
        hZfull0 hhomoFull
  let V : Matrix lb lb ℝ :=
    twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A
  have hGaussian :
      TwoSLSSubsetResidualizedGaussianCriterionInputs μ Za Zb X Y V := by
    simpa [V, Zfull] using
      TwoSLSSubsetResidualizedGaussianCriterionInputs.of_assumption12_2_fullResidualScoreMap_covarianceTarget_neweyCovariance_rankProbability
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (A := A) hFullMixed β hFull.model hrank hA hcov
        (twoSLSSubsetLimitResidualizedScoreMap_fullRowRank_of_rowGram_det_isUnit
          μ Za Zb X A (by
            simpa [A, Zfull] using
              twoSLSSubsetLimitResidualizedScoreMap_rowGram_det_isUnit_of_observed_assumption12_2
                (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e)
                hMaintained hFull))
  have hnum : BoundedInProbability μ
      (fun m ω =>
        twoSLSSarganNumeratorStar
          (stackRegressors Za m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)) :=
    twoSLSSarganNumeratorStar_bounded_of_assumption12_2_homoskedastic
      (μ := μ) (Z := Za) (X := X) (e := e) (Y := Y)
      hover hMaintainedMixed β hMaintained.model hZa0 hhomo hsigma_pos
  have hdiff : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) :=
    twoSLSSubsetCommonSigmaDiff_tendstoInMeasure_zero_of_assumption12_2_bounded
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      hnum hMaintainedMixed hFullMixed β hMaintained.model (ne_of_gt hsigma_pos)
  have hnewey_ne_common : Tendsto
      (fun m => μ {ω |
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) ≠
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hrank.all (Eventually.of_forall fun _ => zero_le _) ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    refine measure_mono ?_
    intro ω hneq
    by_contra hbad
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hbad
    classical
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) :=
      Matrix.invertibleOfIsUnitDet
        (A := (stackRegressors Za m ω)ᵀ * stackRegressors Za m ω) hbad.1.1
    letI : Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω)) :=
      Matrix.invertibleOfIsUnitDet
        (A := (Matrix.fromCols (stackRegressors Za m ω)
            (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        hbad.1.2
    have hMaintainedMoment : IsUnit
        (twoSLSMomentMatrixStar
          (stackRegressors Za m ω) (stackRegressors X m ω)).det :=
      isUnit_twoSLSMomentMatrixStar_det_of_sample_bread
        (stackRegressors Za m ω) (stackRegressors X m ω) hbad.2.1
    have hFullMoment : IsUnit
        (twoSLSMomentMatrixStar
          (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
          (stackRegressors X m ω)).det :=
      isUnit_twoSLSMomentMatrixStar_det_of_sample_bread
        (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (stackRegressors X m ω) hbad.2.2
    have hMaintainedFitted : Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))) := by
      refine ⟨Matrix.invertibleOfIsUnitDet
        (A := (fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω)) ?_⟩
      have heq :=
        fittedRegressorsStar_transpose_mul_self_eq_twoSLSMomentMatrixStar_generic
        (Z := stackRegressors Za m ω) (X := stackRegressors X m ω)
      rw [congrArg Matrix.det heq]
      exact hMaintainedMoment
    have hFullFitted : Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))) := by
      refine ⟨Matrix.invertibleOfIsUnitDet
        (A := (fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω)) ?_⟩
      have heq :=
        fittedRegressorsStar_transpose_mul_self_eq_twoSLSMomentMatrixStar_generic
        (Z := Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
        (X := stackRegressors X m ω)
      rw [congrArg Matrix.det heq]
      exact hFullMoment
    exact hneq
      (twoSLSSubsetNeweyStatOrZero_eq_commonSigmaStat_of_gramBranches
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)
        ⟨inferInstance⟩ ⟨inferInstance⟩ hFullFitted hMaintainedFitted)
  have hZa_meas : ∀ i, AEStronglyMeasurable (Za i) μ :=
    hMaintainedMixed.z_aestronglyMeasurable
  have hX_meas : ∀ i, AEStronglyMeasurable (X i) μ :=
    hMaintainedMixed.x_aestronglyMeasurable
  have hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      hMaintainedMixed.x_aestronglyMeasurable
      hMaintainedMixed.e_aestronglyMeasurable hMaintained.model
  have hZb_meas : ∀ i, AEStronglyMeasurable (Zb i) μ := by
    intro i
    rw [aestronglyMeasurable_iff_aemeasurable]
    refine aemeasurable_pi_lambda (Zb i) ?_
    intro b
    have hb : AEMeasurable (fun ω => Zfull i ω (Sum.inr b)) μ :=
      (measurable_pi_apply (Sum.inr b)).comp_aemeasurable
        (hFullMixed.z_aestronglyMeasurable i).aemeasurable
    simpa [Zfull] using hb
  let T : ℕ → Ω → lb → ℝ := fun m ω =>
    (Real.sqrt (m : ℝ))⁻¹ •
      twoSLSSubsetResidualizedScoreStar
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)
  let Vhat : ℕ → Ω → Matrix lb lb ℝ := fun m ω =>
    twoSLSSubsetNeweyCriterionCovHatStar
      (stackRegressors Za m ω) (stackRegressors Zb m ω)
      (stackRegressors X m ω) (stackOutcomes Y m ω)
  have hV_meas : ∀ m, AEStronglyMeasurable (Vhat m) μ := by
    intro m
    simpa [Vhat, stackRegressors, stackOutcomes] using
      twoSLSSubsetNeweyCriterionCovHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
        hZa_meas hZb_meas hX_meas hY_meas m
  have hV_nonsing : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det V).mp hGaussian.covariance_posDef.isUnit
  have hlb_pos : 0 < Fintype.card lb := by
    rw [← hdf]
    exact Fact.out
  have hLawCard :
      HasLaw
        (fun z : EuclideanSpace ℝ lb =>
          (z : lb → ℝ) ⬝ᵥ (V⁻¹ *ᵥ (z : lb → ℝ)))
        (chiSquared (Fintype.card lb)) (multivariateGaussian 0 V) :=
    hasLaw_multivariateGaussian_zero_mahalanobis_chiSquared_fintype
      (ι := lb) hlb_pos hGaussian.covariance_posDef
  have hLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ lb => z.ofLp ⬝ᵥ (V⁻¹ *ᵥ z.ofLp))
        (chiSquared df) (multivariateGaussian 0 V) := by
    simpa [hdf] using hLawCard
  have hcriterion : TendstoInDistribution
      (fun m ω => criterionJStatOrZero (T m ω) (Vhat m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := μ) (ν := multivariateGaussian 0 V) (df := df) (k := lb)
      (T := T) (Z := fun z : EuclideanSpace ℝ lb => z.ofLp)
      (Vhat := Vhat) (V := V)
      (by simpa [T] using hGaussian.score_clt) hV_meas
      (by simpa [Vhat, V] using hGaussian.covariance_tendsto)
      hV_nonsing hLaw
  have hnewey : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
    refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hcriterion
    intro m
    exact ae_of_all μ fun ω => by
      simpa [T, Vhat] using
        (twoSLSSubsetNeweyStatOrZero_eq_criterionJStatOrZero_residualizedScore
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)).symm
  have hcommon : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) := by
    have hcommon_meas : ∀ m, AEMeasurable
        (fun ω =>
          twoSLSSubsetSarganDiffCommonSigmaStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
      intro m
      simpa [stackRegressors, stackOutcomes] using
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero_aemeasurable_of_rows
          (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
          hZa_meas hZb_meas hX_meas hY_meas m
    have hcommon_sub_newey : TendstoInMeasure μ
        ((fun (m : ℕ) ω =>
          twoSLSSubsetSarganDiffCommonSigmaStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) -
         (fun (m : ℕ) ω =>
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)))
        atTop (fun _ => 0) :=
      tendstoInMeasure_sub_zero_of_measure_ne_tendsto_zero hnewey_ne_common
    exact tendstoInDistribution_of_tendstoInMeasure_sub
      (X := fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Y := fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Z := fun x : ℝ => x) hnewey hcommon_sub_newey hcommon_meas
  have hsargan_meas : ∀ m, AEMeasurable
      (fun ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      twoSLSSubsetSarganDiffStatOrZero_aemeasurable_of_rows
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
        hZa_meas hZb_meas hX_meas hY_meas m
  have hdiff_rev : TendstoInMeasure μ
      ((fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)) -
       (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)))
      atTop (fun _ => 0) := by
    simpa [Pi.sub_apply, sub_eq_add_neg, add_comm] using
      TendstoInMeasure.neg_zero_real hdiff
  have hsargan : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) :=
    tendstoInDistribution_of_tendstoInMeasure_sub
      (X := fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Y := fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (Z := fun x : ℝ => x) hcommon hdiff_rev hsargan_meas
  have hequiv : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) := by
    have hcommon_sub_newey : TendstoInMeasure μ
        ((fun (m : ℕ) ω =>
          twoSLSSubsetSarganDiffCommonSigmaStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) -
         (fun (m : ℕ) ω =>
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)))
        atTop (fun _ => 0) :=
      tendstoInMeasure_sub_zero_of_measure_ne_tendsto_zero hnewey_ne_common
    have hnewey_sub_common : TendstoInMeasure μ
        ((fun (m : ℕ) ω =>
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)) -
         (fun (m : ℕ) ω =>
          twoSLSSubsetSarganDiffCommonSigmaStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)))
        atTop (fun _ => 0) := by
      simpa [Pi.sub_apply, sub_eq_add_neg, add_comm] using
        TendstoInMeasure.neg_zero_real hcommon_sub_newey
    simpa [Pi.sub_apply, sub_eq_add_neg, add_assoc] using
      TendstoInMeasure.add_zero_real hnewey_sub_common hdiff
  have hNsize :=
    chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
      (μ := μ)
      (W := fun m ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (q := df) (crit := crit) (alpha := alpha) hcrit hnewey
  have hCsize :=
    chiSquaredTest_rejectionProb_tendsto_alpha_of_stat
      (μ := μ)
      (W := fun m ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      (q := df) (crit := crit) (alpha := alpha) hcrit hsargan
  exact ⟨hnewey_ne_common, hnewey, hsargan, hequiv, hNsize, hCsize⟩

set_option linter.style.longLine false in
/-- Lower-tail critical-value convention for
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos`. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hrank : TwoSLSSubsetRankFailureProbabilityConditions μ Za Zb X)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    Tendsto
      (fun m => μ {ω |
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) ≠
        twoSLSSubsetSarganDiffCommonSigmaStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    hover hdf hMaintained hFull hZa0 hZfull0 hhomoFull
    hrank
    (chiSquared_upperTail_eq_of_lowerTail_eq
      (q := df) (c := crit) (alpha := alpha) halpha_le_one hcrit)

namespace Theorem12_17

set_option linter.style.longLine false in
/-- Canonical observed-row endpoint for Hansen Theorem 12.17.

Observed Assumption 12.2 derives both the limiting row rank and the vanishing
probabilities of all singular finite-sample branches. -/
abbrev observed
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)] {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 : Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull : HomoskedasticErrorVariance μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    hover hdf hMaintained hFull hZa0 hZfull0 hhomoFull
    (TwoSLSSubsetRankFailureProbabilityConditions.of_observed_assumption12_2
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      hMaintained hFull)
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail critical-value companion to `Theorem12_17.observed`. -/
abbrev observed_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)] {β : k → ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 : Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull : HomoskedasticErrorVariance μ
      (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :=
  twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullInstrumentSampleGram_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_derivedSigmaPos_lowerTail
    (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
    hover hdf hMaintained hFull hZa0 hZfull0 hhomoFull
    (TwoSLSSubsetRankFailureProbabilityConditions.of_observed_assumption12_2
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
      hMaintained hFull)
    halpha_le_one hcrit

end Theorem12_17

set_option linter.style.longLine false in
/-- Observed-row facade for Hansen Theorem 12.17's probability-level
asymptotic equivalence between Newey's subset test and the Sargan-difference
subset test.

This reuses the same full-homoskedastic Newey-covariance route as
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams`,
then applies the generic rejection-probability equivalence bridge with
textbook degrees of freedom `ℓ_b`. -/
theorem
    twoSLSSubsetNeweySarganDiffTest_rejectionProb_equiv_card_of_normalEquations_fullResidualScoreMap_covarianceTarget_fullHomoskedastic_neweyCovariance_rowGram_assumption12_2_observed_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    [Fact (0 < Fintype.card lb)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hMaintained :
      TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hZfull0 :
      Measurable (fun ω => Sum.elim (Za 0 ω) (Zb 0 ω)))
    [SigmaFinite (μ.trim (conditioningSpace_le hZfull0))]
    (hhomoFull :
      HomoskedasticErrorVariance μ
        (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hR_rowGram : IsUnit
      ((twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A) *
        (twoSLSSubsetLimitResidualizedScoreMap μ Za Zb X A)ᵀ).det)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Ioi crit) = alpha) :
    Tendsto
      (fun m =>
        μ {ω | crit <
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)} -
        μ {ω | crit <
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) ∧
    Tendsto
      (fun m =>
        μ {ω | crit <
          twoSLSSubsetSarganDiffStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)} -
        μ {ω | crit <
          twoSLSSubsetNeweyStatOrZero
            (stackRegressors Za m ω) (stackRegressors Zb m ω)
            (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 0) := by
  have hhomo : HomoskedasticErrorVariance μ Za e :=
    HomoskedasticErrorVariance.of_twoSLSCombined_left
      (μ := μ) (Za := Za) (Zb := Zb) (e := e) hZfull0 hhomoFull
  have hcov :
      scoreCovMat μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) e =
        errorVariance μ e •
          twoSLSCombinedQZZ
            (popGram μ (twoSLSCombinedRegressors
              (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X)) :=
    scoreCovMat_eq_errorVariance_smul_twoSLSCombinedQZZ_of_assumption12_2_homoskedastic
      (μ := μ) (Z := fun i ω => Sum.elim (Za i ω) (Zb i ω))
      (X := X) (e := e)
      hFull.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions
      hZfull0 hhomoFull
  exact
    twoSLSSubsetNeweySarganDiffTest_rejectionProb_equiv_card
      (μ := μ) (Za := Za) (Zb := Zb) (X := X) (Y := Y)
      (TwoSLSSubsetOveridConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_neweyCovariance_rowGram_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (A := A) hover rfl hMaintained.toResidualTextbookFourthConditions
        hFull.toResidualTextbookFourthConditions hZa0 hhomo hsigma_pos
        hZa hZ hFitted hMaintainedFitted hA hcov hR_rowGram)
      hcrit

set_option linter.style.longLine false in
/-- Theorem 12.17 facade with the limiting covariance regularity stated
directly on Hansen's displayed residualized-score covariance target.

This is the upper-tail critical-value counterpart of
`twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_posDef_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail`.
It removes the manual step of building the Slutsky bridge package before citing
the full Theorem 12.17 conclusion. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_posDef_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hV_pos :
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.toSubsetOveridConditions
      (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_posDef_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
        hZa hZ hFitted hMaintainedFitted hA hV hV_pos))
    hcrit

set_option linter.style.longLine false in
/-- Lower-tail Theorem 12.17 facade with the limiting covariance regularity
stated directly on Hansen's displayed residualized-score covariance target.

This reuses the strongest common-sigma constructor: literal finite-fourth
Assumption 12.2 packages supply the residualized-score CLT route, while
maintained/full instrument Grams and maintained/full fitted-regressor Grams
derive the finite-sample residualized and moment nonsingularity branches. -/
theorem
    twoSLSSubsetOverid_theorem12_17_of_normalEquations_fullResidualScoreMap_covarianceTarget_posDef_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams_lowerTail
    {Za : ℕ → Ω → la → ℝ} {Zb : ℕ → Ω → lb → ℝ}
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {df : ℕ} [Fact (0 < df)]
    {β : k → ℝ} {A : Matrix lb (la ⊕ lb) ℝ}
    (hover : Fintype.card k < Fintype.card la)
    (hdf : df = Fintype.card lb)
    (hMaintained :
      TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Za X e Y β)
    (hFull : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
      μ (fun i ω => Sum.elim (Za i ω) (Zb i ω)) X e Y β)
    (hZa0 : Measurable (Za 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hZa0))]
    (hhomo : HomoskedasticErrorVariance μ Za e)
    (hsigma_pos : 0 < errorVariance μ e)
    (hZa : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((stackRegressors Za m ω)ᵀ * stackRegressors Za m ω)))
    (hZ : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))ᵀ *
          Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))))
    (hFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (Matrix.fromCols (stackRegressors Za m ω) (stackRegressors Zb m ω))
            (stackRegressors X m ω))))
    (hMaintainedFitted : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible
        ((fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))ᵀ *
          fittedRegressorsStar
            (stackRegressors Za m ω) (stackRegressors X m ω))))
    (hA : TendstoInMeasure μ
      (fun m ω =>
        twoSLSSubsetResidualizedScoreMapStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω))
      atTop (fun _ => A))
    (hV : TendstoInMeasure μ
      (fun (m : ℕ) (ω : Ω) =>
        twoSLSSubsetNeweyCriterionCovHatStar
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
        (fun _ => twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A))
    (hV_pos :
      (twoSLSSubsetResidualizedScoreCovariance μ Za Zb X e A).PosDef)
    {crit : ℝ} {alpha : ℝ≥0∞}
    (halpha_le_one : alpha ≤ 1)
    (hcrit : (chiSquared df) (Set.Iic crit) = 1 - alpha) :
    (∀ (m : ℕ) (ω : Ω),
      twoSLSSubsetNeweyStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω) =
      twoSLSSubsetSarganDiffCommonSigmaStatOrZero
        (stackRegressors Za m ω) (stackRegressors Zb m ω)
        (stackRegressors X m ω) (stackOutcomes Y m ω)) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared df) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω) -
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => 0) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetNeweyStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) ∧
    Tendsto
      (fun m => μ {ω | crit <
        twoSLSSubsetSarganDiffStatOrZero
          (stackRegressors Za m ω) (stackRegressors Zb m ω)
          (stackRegressors X m ω) (stackOutcomes Y m ω)})
      atTop (𝓝 alpha) :=
  twoSLSSubsetOverid_theorem12_17_lowerTail
    (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.toSubsetOveridConditions
      (TwoSLSSubsetCommonSigmaSlutskyBridgeConditions.of_normalEquations_fullResidualScoreMap_covarianceTarget_posDef_assumption12_2_textbookFourth_homoskedastic_derivedDualSchur_fullGram_fittedGrams
        (μ := μ) (Za := Za) (Zb := Zb) (X := X) (e := e) (Y := Y)
        (A := A) hover hdf hMaintained hFull hZa0 hhomo hsigma_pos
        hZa hZ hFitted hMaintainedFitted hA hV hV_pos))
    halpha_le_one hcrit

end Asymptotics

end HansenEconometrics
