import HansenEconometrics.Chapter13GMM.Inference

/-!
# Chapter 13 — distance and specification tests

This module contains Hansen Theorems 13.12--13.17. The deterministic distance
results use the quadratic-completion lemma in `Chapter13GMM.Primitives`. The
distributional results reuse Chapter 9's feasible quadratic-form theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory
  ProbabilityTheory ENNReal

namespace HansenEconometrics

@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    {i j : Type*} [Fintype i] [Fintype j] :
    MeasurableSpace (Matrix i j ℝ) :=
  matrixBorelMeasurableSpace i j

private lemma matrixBorelSpaceInst
    {i j : Type*} [Fintype i] [Fintype j] :
    @BorelSpace (Matrix i j ℝ) _
      (matrixBorelMeasurableSpaceInst (i := i) (j := j)) :=
  matrixBorelSpace i j

attribute [local instance] matrixBorelMeasurableSpaceInst matrixBorelSpaceInst

/-! ## GMM criterion and distance -/

/-- GMM criterion based on normalized sample moments `n⁻¹Z'(Y-Xb)`. -/
noncomputable def gmmNormalizedCriterion
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) : ℝ :=
  LinearGMM.criterion (sampleQZX Z X) (sampleCrossMoment Z y) W b

/-- Hansen's sample criterion `n gbar(b)' W gbar(b)`. -/
noncomputable def gmmCriterionValue
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) : ℝ :=
  (Fintype.card n : ℝ) * gmmNormalizedCriterion X Z y W b

/-- Hansen's GMM distance statistic: restricted criterion minus unrestricted
criterion. The two coefficients may use different construction procedures,
but this definition uses the displayed common weight `W`. -/
noncomputable def gmmDistanceStat
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (btilde bhat : k → ℝ) : ℝ :=
  gmmCriterionValue X Z y W btilde -
    gmmCriterionValue X Z y W bhat

/-- Efficient minimum-distance criterion for a linear restriction equals the
corresponding Wald quadratic form. -/
theorem emdJStatOrZero_eq_restrictionWaldStatOrZero
    {k : Type*} {r : ℕ} [Fintype k] [DecidableEq k]
    (R : Matrix k (Fin r) ℝ) (c : Fin r → ℝ) (V : Matrix k k ℝ)
    (bhat : k → ℝ) (root : ℝ)
    (hV : V.PosDef) (hR : Function.Injective R.mulVec) :
    emdJStatOrZero V bhat (emdBetaStar R c V bhat) root =
      restrictionWaldStatOrZero
        (root • (Rᵀ *ᵥ bhat - c)) (Rᵀ * V * R) := by
  let G : Matrix (Fin r) (Fin r) ℝ := Rᵀ * V * R
  let A : Matrix (Fin r) (Fin r) ℝ := G⁻¹
  let B : Matrix k (Fin r) ℝ := V * R * A
  let u : Fin r → ℝ := root • (Rᵀ *ᵥ bhat - c)
  have hVunit : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit
  have hVsym : Vᵀ = V :=
    (Matrix.conjTranspose_eq_transpose_of_trivial V).symm.trans
      hV.isHermitian.eq
  have hGunit : IsUnit G.det := by
    simpa [G] using restrictionCov_det_isUnit_of_cov_posDef V R hV hR
  have hAsym : Aᵀ = A := by
    dsimp [A, G]
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
      Matrix.transpose_mul, hVsym,
      Matrix.transpose_transpose]
    simp [Matrix.mul_assoc]
  have hAGA : A * G * A = A := by
    calc
      A * G * A = A * (G * A) := by simp [Matrix.mul_assoc]
      _ = A := by rw [Matrix.mul_nonsing_inv G hGunit]; simp
  have hdiff :
      root • (bhat - emdBetaStar R c V bhat) = B *ᵥ u := by
    rw [emdBetaStar_eq_hansen R c V bhat hVunit]
    simp [B, A, G, u, Matrix.mulVec_smul]
  have hpull : Bᵀ * V⁻¹ * B = A := by
    dsimp [B]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hAsym,
      hVsym]
    calc
      A * (Rᵀ * V) * V⁻¹ * (V * R * A) =
          A * Rᵀ * (V * V⁻¹) * V * R * A := by
            simp [Matrix.mul_assoc]
      _ = A * Rᵀ * V * R * A := by
        rw [Matrix.mul_nonsing_inv V hVunit]
        simp [Matrix.mul_assoc]
      _ = A * G * A := by simp [G, Matrix.mul_assoc]
      _ = A := hAGA
  unfold emdJStatOrZero criterionJStatOrZero
    restrictionWaldStatOrZero
  rw [hdiff, quadraticForm_mulVec_eq_pullback_rect, hpull]

/-- **Hansen Theorem 13.13, first clause.** With a common weight matrix, the
constrained criterion cannot be below the unrestricted GMM minimum. -/
theorem gmmDistanceStat_nonneg_of_commonWeight
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [Nonempty n] [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (btilde : k → ℝ)
    [Invertible (gmmNormalizedGram X Z W)]
    (hW : W.PosSemidef) :
    0 ≤ gmmDistanceStat X Z y W btilde
      (gmmBetaOrZero X Z y W) := by
  letI : Invertible
      (LinearGMM.gram (sampleQZX Z X) W) := by
    simpa [gmmNormalizedGram] using
      (inferInstance : Invertible (gmmNormalizedGram X Z W))
  have hbeta : gmmBetaOrZero X Z y W =
      LinearGMM.beta (sampleQZX Z X) (sampleCrossMoment Z y) W := by
    rw [gmmBetaOrZero_eq_gmmBetaStar,
      gmmBetaStar_eq_normalized X Z y W]
    exact LinearGMM.betaStar_eq_beta
      (sampleQZX Z X) (sampleCrossMoment Z y) W
  have hmin := LinearGMM.beta_minimizes
    (sampleQZX Z X) (sampleCrossMoment Z y) W btilde hW
  unfold gmmDistanceStat gmmCriterionValue gmmNormalizedCriterion
  rw [hbeta]
  rw [← mul_sub]
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hmin)

/-- **Hansen Theorem 13.13, second clause.** With a common efficient weight
and a linear restriction, the GMM distance statistic equals the Wald
statistic exactly. -/
theorem gmmDistanceStat_eq_wald_of_linear_commonWeight
    {n k l : Type*} {r : ℕ}
    [Fintype n] [Fintype k] [Fintype l] [Nonempty n]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (R : Matrix k (Fin r) ℝ) (c : Fin r → ℝ)
    (hW : W.PosSemidef)
    (hG : (gmmNormalizedGram X Z W).PosDef)
    (hR : Function.Injective R.mulVec) :
    gmmDistanceStat X Z y W
        (gmmConstrainedBetaStar X Z y W R c)
        (gmmBetaOrZero X Z y W) =
      restrictionWaldStatOrZero
        (Real.sqrt (Fintype.card n : ℝ) •
          (Rᵀ *ᵥ gmmBetaOrZero X Z y W - c))
        (Rᵀ * (gmmNormalizedGram X Z W)⁻¹ * R) := by
  let G : Matrix k k ℝ := gmmNormalizedGram X Z W
  let bhat : k → ℝ := gmmBetaOrZero X Z y W
  let btilde : k → ℝ := gmmConstrainedBetaStar X Z y W R c
  let root : ℝ := Real.sqrt (Fintype.card n : ℝ)
  have hGunit : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (by simpa [G] using hG.isUnit)
  letI : Invertible G :=
    Matrix.invertibleOfIsUnitDet (A := G) hGunit
  letI : Invertible
      (LinearGMM.gram (sampleQZX Z X) W) := by
    simpa [G, gmmNormalizedGram] using (inferInstance : Invertible G)
  have hbeta : bhat =
      LinearGMM.beta (sampleQZX Z X) (sampleCrossMoment Z y) W := by
    dsimp [bhat]
    rw [gmmBetaOrZero_eq_gmmBetaStar,
      gmmBetaStar_eq_normalized X Z y W]
    exact LinearGMM.betaStar_eq_beta
      (sampleQZX Z X) (sampleCrossMoment Z y) W
  have hcompletion := LinearGMM.criterion_eq_at_beta_add_quadratic_form
    (sampleQZX Z X) (sampleCrossMoment Z y) W btilde hW
  have hcriterion :
      gmmNormalizedCriterion X Z y W btilde -
          gmmNormalizedCriterion X Z y W bhat =
        (btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat)) := by
    have hc :
        gmmNormalizedCriterion X Z y W btilde =
          gmmNormalizedCriterion X Z y W bhat +
            (btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat)) := by
      simpa [gmmNormalizedCriterion, G, hbeta] using hcompletion
    linarith
  have hbtilde : btilde = emdBetaStar R c G⁻¹ bhat := by
    simp [btilde, bhat, gmmConstrainedBetaStar, emdBetaStar, G,
      Matrix.nonsing_inv_nonsing_inv G hGunit]
  have hscale :
      (Fintype.card n : ℝ) *
          ((btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat))) =
        emdJStatOrZero G⁻¹ bhat btilde root := by
    have hsqrt : root ^ 2 = (Fintype.card n : ℝ) := by
      simp [root, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card n))]
    have hdiff : bhat - btilde = -(btilde - bhat) := by
      abel
    rw [← hsqrt]
    unfold emdJStatOrZero criterionJStatOrZero
    rw [Matrix.nonsing_inv_nonsing_inv G hGunit]
    rw [hdiff]
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      Matrix.mulVec_neg, neg_dotProduct_neg]
    simp [pow_two, mul_assoc]
  have hemd := emdJStatOrZero_eq_restrictionWaldStatOrZero
    R c G⁻¹ bhat root hG.inv hR
  calc
    gmmDistanceStat X Z y W btilde bhat =
        (Fintype.card n : ℝ) *
          (gmmNormalizedCriterion X Z y W btilde -
            gmmNormalizedCriterion X Z y W bhat) := by
          simp [gmmDistanceStat, gmmCriterionValue, mul_sub]
    _ = (Fintype.card n : ℝ) *
        ((btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat))) := by
          rw [hcriterion]
    _ = emdJStatOrZero G⁻¹ bhat btilde root := hscale
    _ = emdJStatOrZero G⁻¹ bhat (emdBetaStar R c G⁻¹ bhat) root := by
          rw [← hbtilde]
    _ = restrictionWaldStatOrZero
        (root • (Rᵀ *ᵥ bhat - c)) (Rᵀ * G⁻¹ * R) := hemd
    _ = restrictionWaldStatOrZero
        (Real.sqrt (Fintype.card n : ℝ) •
          (Rᵀ *ᵥ gmmBetaOrZero X Z y W - c))
        (Rᵀ * (gmmNormalizedGram X Z W)⁻¹ * R) := by
          rfl

/-! ## Hansen Theorem 13.12 -/

/-- **Hansen Theorem 13.12.** If the distance statistic differs from the
Chapter 13.8 Wald statistic by `o_p(1)`, it has the same chi-square limit. The
distance/Wald equivalence is the Assumption 7.3 linearization obligation. -/
theorem gmmDistanceStat_tendstoInDistribution_chiSquared
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {r : ℕ} [Fact (0 < r)]
    (D Wald : ℕ → OmegaSpace → ℝ)
    (hWald : TendstoInDistribution Wald atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared r))
    (hrem : TendstoInMeasure mu (D - Wald) atTop (fun _ => 0))
    (hD_meas : ∀ n, AEMeasurable (D n) mu) :
    TendstoInDistribution D atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared r) :=
  tendstoInDistribution_of_tendstoInMeasure_sub
    (X := Wald) (Y := D) (Z := fun x : ℝ => x)
    hWald hrem hD_meas

/-- Size form of Hansen Theorem 13.12. -/
theorem gmmDistanceTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {r : ℕ} [Fact (0 < r)]
    {D : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha)
    (hD : TendstoInDistribution D atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared r)) :
    Tendsto (fun n => mu {omega | crit < D n omega}) atTop
      (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hD

/-! ## Hansen J and subset specification tests -/

/-- Hansen's efficient-GMM `J` statistic at the reusable score layer. The
input is the scaled residual sample moment and `OmegaHat` estimates its
covariance. -/
noncomputable def gmmJStatOrZero
    {l : Type*} [Fintype l] [DecidableEq l]
    (scaledResidualMoment : l → ℝ) (OmegaHat : Matrix l l ℝ) : ℝ :=
  criterionJStatOrZero scaledResidualMoment OmegaHat

/-- **Hansen Theorem 13.14.** A feasible efficient-GMM score quadratic has
the chi-square overidentification limit once the residual-score limit and its
rank law are supplied. The usual degrees of freedom are `card l - card k`. -/
theorem gmmJStatOrZero_tendstoInDistribution_chiSquared
    {OmegaSpace OmegaLimit : Type*}
    [MeasurableSpace OmegaSpace] [MeasurableSpace OmegaLimit]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {nu : Measure OmegaLimit} [IsProbabilityMeasure nu]
    {l : Type*} [Fintype l] [DecidableEq l]
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → OmegaSpace → l → ℝ} {G : OmegaLimit → l → ℝ}
    {OmegaHat : ℕ → OmegaSpace → Matrix l l ℝ}
    {Omega : Matrix l l ℝ}
    (hT : TendstoInDistribution T atTop G (fun _ => mu) nu)
    (hOmega_meas : ∀ n, AEStronglyMeasurable (OmegaHat n) mu)
    (hOmega : TendstoInMeasure mu OmegaHat atTop (fun _ => Omega))
    (hOmega_nonsing : IsUnit Omega.det)
    (hLaw : HasLaw
      (fun omega => G omega ⬝ᵥ (Omega⁻¹ *ᵥ G omega))
      (chiSquared df) nu) :
    TendstoInDistribution
      (fun n omega => gmmJStatOrZero (T n omega) (OmegaHat n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  simpa [gmmJStatOrZero] using
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := mu) (ν := nu) (df := df)
      (T := T) (Z := G) (Vhat := OmegaHat) (V := Omega)
      hT hOmega_meas hOmega hOmega_nonsing hLaw

/-- Size form of Hansen Theorem 13.14. -/
theorem gmmJTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {J : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hJ : TendstoInDistribution J atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {omega | crit < J n omega}) atTop
      (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hJ

/-- Difference between the full and maintained efficient-GMM criteria. -/
noncomputable def gmmSubsetOveridentificationStatOrZero
    (fullJ maintainedJ : ℝ) : ℝ :=
  fullJ - maintainedJ

/-- **Hansen Theorem 13.15.** The subset overidentification statistic has a
chi-square limit when its residualized score has the feasible quadratic-form
limit. The rank assumption in the textbook supplies the nonsingularity and
limiting rank-law premises below. -/
theorem gmmSubsetOveridentificationStatOrZero_tendstoInDistribution_chiSquared
    {OmegaSpace OmegaLimit : Type*}
    [MeasurableSpace OmegaSpace] [MeasurableSpace OmegaLimit]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {nu : Measure OmegaLimit} [IsProbabilityMeasure nu]
    {df : ℕ} [Fact (0 < df)]
    {fullJ maintainedJ : ℕ → OmegaSpace → ℝ}
    {T : ℕ → OmegaSpace → Fin df → ℝ}
    {G : OmegaLimit → Fin df → ℝ}
    {Vhat : ℕ → OmegaSpace → Matrix (Fin df) (Fin df) ℝ}
    {V : Matrix (Fin df) (Fin df) ℝ}
    (hT : TendstoInDistribution T atTop G (fun _ => mu) nu)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu)
    (hV : TendstoInMeasure mu Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun omega => G omega ⬝ᵥ (V⁻¹ *ᵥ G omega))
      (chiSquared df) nu)
    (hbridge : TendstoInMeasure mu
      (fun n omega =>
        gmmSubsetOveridentificationStatOrZero
            (fullJ n omega) (maintainedJ n omega) -
          criterionJStatOrZero (T n omega) (Vhat n omega))
      atTop (fun _ => 0))
    (hC_meas : ∀ n, AEMeasurable
      (fun omega => gmmSubsetOveridentificationStatOrZero
        (fullJ n omega) (maintainedJ n omega)) mu) :
    TendstoInDistribution
      (fun n omega => gmmSubsetOveridentificationStatOrZero
        (fullJ n omega) (maintainedJ n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  have hcriterion :=
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := mu) (ν := nu) (df := df)
      (T := T) (Z := G) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_nonsing hLaw
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n omega => criterionJStatOrZero (T n omega) (Vhat n omega))
    (Y := fun n omega => gmmSubsetOveridentificationStatOrZero
      (fullJ n omega) (maintainedJ n omega))
    (Z := fun x : ℝ => x) hcriterion hbridge hC_meas

/-- Size form of Hansen Theorem 13.15. -/
theorem gmmSubsetOveridentificationTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {C : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hC : TendstoInDistribution C atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {omega | crit < C n omega}) atTop
      (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hC

/-- GMM endogeneity statistic, defined as the corresponding subset
overidentification criterion difference. -/
noncomputable def gmmEndogeneityStatOrZero
    (augmentedJ maintainedJ : ℝ) : ℝ :=
  gmmSubsetOveridentificationStatOrZero augmentedJ maintainedJ

/-- **Hansen Theorem 13.16.** The GMM endogeneity test is Theorem 13.15 with
the tested regressors added to the instrument set. -/
theorem gmmEndogeneityStatOrZero_tendstoInDistribution_chiSquared
    {OmegaSpace OmegaLimit : Type*}
    [MeasurableSpace OmegaSpace] [MeasurableSpace OmegaLimit]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {nu : Measure OmegaLimit} [IsProbabilityMeasure nu]
    {df : ℕ} [Fact (0 < df)]
    {augmentedJ maintainedJ : ℕ → OmegaSpace → ℝ}
    {T : ℕ → OmegaSpace → Fin df → ℝ}
    {G : OmegaLimit → Fin df → ℝ}
    {Vhat : ℕ → OmegaSpace → Matrix (Fin df) (Fin df) ℝ}
    {V : Matrix (Fin df) (Fin df) ℝ}
    (hT : TendstoInDistribution T atTop G (fun _ => mu) nu)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu)
    (hV : TendstoInMeasure mu Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun omega => G omega ⬝ᵥ (V⁻¹ *ᵥ G omega))
      (chiSquared df) nu)
    (hbridge : TendstoInMeasure mu
      (fun n omega =>
        gmmEndogeneityStatOrZero
            (augmentedJ n omega) (maintainedJ n omega) -
          criterionJStatOrZero (T n omega) (Vhat n omega))
      atTop (fun _ => 0))
    (hC_meas : ∀ n, AEMeasurable
      (fun omega => gmmEndogeneityStatOrZero
        (augmentedJ n omega) (maintainedJ n omega)) mu) :
    TendstoInDistribution
      (fun n omega => gmmEndogeneityStatOrZero
        (augmentedJ n omega) (maintainedJ n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  simpa [gmmEndogeneityStatOrZero] using
    gmmSubsetOveridentificationStatOrZero_tendstoInDistribution_chiSquared
      (mu := mu) (nu := nu) (df := df)
      (fullJ := augmentedJ) (maintainedJ := maintainedJ)
      (T := T) (G := G) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_nonsing hLaw hbridge hC_meas

/-- Size form of Hansen Theorem 13.16. -/
theorem gmmEndogeneityTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {C : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hC : TendstoInDistribution C atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {omega | crit < C n omega}) atTop
      (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hC

/-- GMM subset-endogeneity statistic, again represented by a subset
overidentification criterion difference. -/
noncomputable def gmmSubsetEndogeneityStatOrZero
    (augmentedJ maintainedJ : ℝ) : ℝ :=
  gmmSubsetOveridentificationStatOrZero augmentedJ maintainedJ

/-- **Hansen Theorem 13.17.** The subset endogeneity test is the same subset
overidentification theorem after the instrument augmentation is restricted to
the tested regressor block. -/
theorem gmmSubsetEndogeneityStatOrZero_tendstoInDistribution_chiSquared
    {OmegaSpace OmegaLimit : Type*}
    [MeasurableSpace OmegaSpace] [MeasurableSpace OmegaLimit]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {nu : Measure OmegaLimit} [IsProbabilityMeasure nu]
    {df : ℕ} [Fact (0 < df)]
    {augmentedJ maintainedJ : ℕ → OmegaSpace → ℝ}
    {T : ℕ → OmegaSpace → Fin df → ℝ}
    {G : OmegaLimit → Fin df → ℝ}
    {Vhat : ℕ → OmegaSpace → Matrix (Fin df) (Fin df) ℝ}
    {V : Matrix (Fin df) (Fin df) ℝ}
    (hT : TendstoInDistribution T atTop G (fun _ => mu) nu)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu)
    (hV : TendstoInMeasure mu Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun omega => G omega ⬝ᵥ (V⁻¹ *ᵥ G omega))
      (chiSquared df) nu)
    (hbridge : TendstoInMeasure mu
      (fun n omega =>
        gmmSubsetEndogeneityStatOrZero
            (augmentedJ n omega) (maintainedJ n omega) -
          criterionJStatOrZero (T n omega) (Vhat n omega))
      atTop (fun _ => 0))
    (hC_meas : ∀ n, AEMeasurable
      (fun omega => gmmSubsetEndogeneityStatOrZero
        (augmentedJ n omega) (maintainedJ n omega)) mu) :
    TendstoInDistribution
      (fun n omega => gmmSubsetEndogeneityStatOrZero
        (augmentedJ n omega) (maintainedJ n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  simpa [gmmSubsetEndogeneityStatOrZero] using
    gmmSubsetOveridentificationStatOrZero_tendstoInDistribution_chiSquared
      (mu := mu) (nu := nu) (df := df)
      (fullJ := augmentedJ) (maintainedJ := maintainedJ)
      (T := T) (G := G) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_nonsing hLaw hbridge hC_meas

/-- Size form of Hansen Theorem 13.17. -/
theorem gmmSubsetEndogeneityTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {C : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hC : TendstoInDistribution C atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {omega | crit < C n omega}) atTop
      (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hC

end HansenEconometrics
