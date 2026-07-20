import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space
import HansenEconometrics.ErgodicTheory.PathShift

/-!
# Chapter 14: Wold decomposition — the L² projection-onto-the-past backend

This file provides the Hilbert-space backbone for the Wold decomposition (Hansen §14.14 /
§14.16 / §14.17). It has two layers.

## The abstract Hilbert-space lemma

`Submodule.starProjection_tendsto_iInf_of_antitone` is the antitone (decreasing-family) dual of
Mathlib's `Submodule.starProjection_tendsto_closure_iSup`: for a decreasing sequence of complete
subspaces `U : ℕ → Submodule 𝕜 E` of a Hilbert space, the orthogonal projections of a fixed `x`
onto `U n` converge to the projection of `x` onto `⨅ n, U n`. Mathlib has the increasing version
but not this one; it is proved here by dualising through orthogonal complements
(`W n := (U n)ᗮ` is increasing, `closure (⨆ n, W n) = (⨅ n, U n)ᗮ`, and
`(U n).starProjection x = x - (W n).starProjection x`). This is the engine behind the
remote-past limit `µ_t = lim_{m→∞} P_{t-m}[X_t]` in the Wold theorem (14.17).

## The time-series projection layer

For a real-valued process `X : ℤ → Ω → ℝ` on a finite measure space with each `X s` square
integrable (`hX : ∀ s, MemLp (X s) 2 P`), working inside the Hilbert space `Lp ℝ 2 P`:

* `ProbabilityTheory.oneLp` — the constant-one function as an element of `Lp ℝ 2 P` (an intercept
  for the linear predictor; needs `[IsFiniteMeasure P]`).
* `ProbabilityTheory.pastSpan X P hX t` — the closed linear span of the constant `1` together with
  `{(X s).toLp | s ≤ t}`, i.e. the time-`t` "past" subspace. It is a `topologicalClosure`, hence
  complete, hence has an orthogonal projection (`instance`). Monotone in `t`
  (`pastSpan_mono`), with membership lemmas `toLp_mem_pastSpan`, `oneLp_mem_pastSpan`.
* `ProbabilityTheory.linPred X P hX t` — the linear predictor: the orthogonal projection CLM onto
  `pastSpan X P hX t`.
* `ProbabilityTheory.woldError X P hX t` — the one-step prediction error
  `X_t − linPred_{t−1}(X_t) ∈ Lp ℝ 2 P`. It is orthogonal to the past
  (`woldError_inner_eq_zero_of_mem_pastSpan`) and norm-minimal (`norm_woldError_le`).
* `ProbabilityTheory.projErrorVariance X P hX` — the prediction-error variance `σ² = ‖e₀‖²`
  (for a probability measure this is `E[e₀²] = Var[e₀]`, since `e₀ ⟂ 1`).
* `ProbabilityTheory.remotePast X P hX := ⨅ t : ℤ, pastSpan X P hX t` — the remote (distant) past,
  again with an orthogonal-projection `instance`. The reindexing `iInf_pastSpan_sub` shows that for
  any anchor `t`, `⨅ m : ℕ, pastSpan X P hX (t − m) = remotePast X P hX`, packaging the antitone
  family `fun m => pastSpan X P hX (t − m)` (with `antitone_pastSpan_sub`) for consumption by the
  Wold theorem through `starProjection_tendsto_iInf_of_antitone`.

This is the minimal backend that the projection equation (14.16) and the Wold decomposition
(14.17 / 14.18) build on; the lag-isometry stationarity engine and the theorems themselves are
separate work packages that extend this file.

## The lag isometry and the projection equation (Theorem 14.16)

Strict stationarity is promoted to a *unitary* symmetry of `Lp ℝ 2 (pathLaw X P)` — the lag
operator. Working with the coordinate process `ProbabilityTheory.pathCoord` on path space, the shift
`pathShift ℝ` is measure preserving (`IsStrictlyStationary.measurePreserving_pathShift`), so
composition with it is a surjective linear isometry `ProbabilityTheory.lagIsometryL2`. It advances
the coordinate index by one (`lagIsometryL2_apply_toLp`), fixes the intercept
(`lagIsometryL2_apply_oneLp`), and hence carries the time-`t` past onto the time-`(t+1)` past
(`lagIsometry_map_pastSpan`, via `LinearIsometry.map_starProjection`). Conjugating the projection
through the isometry moves the one-step Wold error forward in time (`lagIsometry_woldError`), which
makes its norm — the prediction-error variance — constant in `t` (`variance_woldError_pathCoord`).

The white-noise properties of the Wold error (Hansen **Theorem 14.16**) are
`integral_woldError_eq_zero` (mean zero), `inner_woldError_woldError_eq_zero` (serial
uncorrelatedness `γ_e(j) = 0` for `j ≥ 1`), and the stationary error variance. The first two hold
for any square-integrable process on the original probability space; only the variance stationarity
consumes the lag isometry, and is therefore stated for the coordinate process on path space.

## The Wold decomposition (Theorems 14.17 and 14.18)

The decomposition itself is assembled on top of this backend, for the coordinate process under
strict stationarity and a non-degenerate innovation variance `σ² > 0`:

* `starProjection_pastSpan_pred` — the one-step innovation projection
  `P_s x = P_{s−1} x + (⟪e_s, x⟫/‖e_s‖²) • e_s`, the atomic step of the projection tower (needs no
  stationarity). Its residual orthogonality is discharged generator-wise via
  `mem_orthogonal_pastSpan_of_generators`, sidestepping any explicit `pastSpan = pastSpan ⊕ ℝ·e`
  subspace decomposition.
* `woldCoeff`, `woldCoeff_eq`, `woldCoeff_zero` — the time-invariant Wold coefficients `b_j` (via
  the lag-isometry cross-moment invariance `inner_woldError_toLp_eq`), with `b_0 = 1`.
* `orthonormal_woldError_smul` — the normalised innovations `σ⁻¹ e_{t−j}` are orthonormal, giving
  Bessel summability `summable_sq_woldCoeff` (`∑_j b_j² < ∞`) and series summability
  `summable_woldError_smul`.
* `starProjection_pastSpan_sub_eq` — the projection tower
  `P_{t−m}[Y_t] = Y_t − ∑_{j<m} b_j e_{t−j}`.
* `woldDeterministic`, `hasSum_woldSeries`, `wold_series_repr` — the deterministic component
  `µ_t = P_{−∞}[Y_t]` and the convergent representation `Y_t = µ_t + ∑_j b_j e_{t−j}`.
* `wold_decomposition` (Hansen **Theorem 14.17**) packages all of this; `IsNonDeterministic` and
  `wold_decomposition_of_nonDeterministic` (Hansen **Theorem 14.18**) specialise to the regular case
  `µ_t = µ · 1`. Hansen's Theorem 14.19 (Wiener–Masani AR(∞) representation) is a documented
  deferral (see the trailing section): it needs a spectral-inversion analytic input absent from
  Mathlib.
-/

open MeasureTheory Filter Topology

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Antitone projection convergence** — the decreasing-family dual of
`Submodule.starProjection_tendsto_closure_iSup`. Given an antitone family `U : ℕ → Submodule 𝕜 E`
of subspaces of a Hilbert space that each admit an orthogonal projection, and with `⨅ n, U n` also
admitting one, the orthogonal projections of a fixed `x` onto `U n` converge to the projection of
`x` onto `⨅ n, U n`.

The proof dualises through orthogonal complements: `W n := (U n)ᗮ` is monotone, its closed
supremum is `(⨅ n, U n)ᗮ`, and `(U n).starProjection x = x − (W n).starProjection x`, so the claim
follows from the increasing-family theorem applied to `W`. -/
theorem starProjection_tendsto_iInf_of_antitone [CompleteSpace E] {U : ℕ → Submodule 𝕜 E}
    (hU : Antitone U) [∀ n, (U n).HasOrthogonalProjection] [(⨅ n, U n).HasOrthogonalProjection]
    (x : E) :
    Tendsto (fun n => (U n).starProjection x) atTop (𝓝 ((⨅ n, U n).starProjection x)) := by
  -- The complements `W n = (U n)ᗮ` form a monotone family.
  have hWmono : Monotone fun n => (U n)ᗮ := fun _ _ hmn => Submodule.orthogonal_le (hU hmn)
  -- The orthogonal complement of the supremum of the `W n` is `⨅ n, U n`.
  have hperp : (⨆ n, (U n)ᗮ)ᗮ = ⨅ n, U n := by
    rw [← Submodule.iInf_orthogonal fun n => (U n)ᗮ]
    exact iInf_congr fun n => Submodule.orthogonal_orthogonal (U n)
  -- Hence the closed supremum of the `W n` is `(⨅ n, U n)ᗮ`.
  have hclosure : (⨆ n, (U n)ᗮ).topologicalClosure = (⨅ n, U n)ᗮ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hperp]
  -- Apply the increasing-family theorem to `W`.
  have hlim := starProjection_tendsto_closure_iSup (fun n => (U n)ᗮ) hWmono x
  -- Rewrite the limit point using `hclosure` (an equality of vectors, not of subspaces).
  have hmemA : (⨆ n, (U n)ᗮ).topologicalClosure.starProjection x ∈ (⨅ n, U n)ᗮ := by
    rw [← hclosure]; exact Submodule.starProjection_apply_mem _ x
  have horthA : x - (⨆ n, (U n)ᗮ).topologicalClosure.starProjection x ∈ ((⨅ n, U n)ᗮ)ᗮ := by
    rw [← hclosure]
    exact Submodule.sub_starProjection_mem_orthogonal
      (K := (⨆ n, (U n)ᗮ).topologicalClosure) x
  have hpoint : (⨆ n, (U n)ᗮ).topologicalClosure.starProjection x
      = (⨅ n, U n)ᗮ.starProjection x :=
    (Submodule.eq_starProjection_of_mem_orthogonal hmemA horthA).symm
  rw [hpoint] at hlim
  -- Convert `x − (W n).starProjection x` back to `(U n).starProjection x`.
  have hfinal : Tendsto (fun n => x - (U n)ᗮ.starProjection x) atTop
      (𝓝 (x - (⨅ n, U n)ᗮ.starProjection x)) := tendsto_const_nhds.sub hlim
  simpa only [starProjection_orthogonal_val, sub_sub_cancel] using hfinal

end Submodule

namespace ProbabilityTheory

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constant-one function as an element of `Lp ℝ 2 P`. Well defined because `P` is finite, so
constants are square integrable. This is the intercept term available to the linear predictor. -/
noncomputable def oneLp (P : Measure Ω) [IsFiniteMeasure P] : Lp ℝ 2 P :=
  MemLp.toLp (fun _ => (1 : ℝ)) (memLp_const 1)

/-- **The time-`t` past subspace.** The closed linear span, inside `Lp ℝ 2 P`, of the constant
function `1` together with the values `{(X s).toLp | s ≤ t}`. This is the subspace onto which
Hansen's linear predictor projects (§14.16). It is defined as a `topologicalClosure`, so it is a
closed subspace of the Hilbert space `Lp ℝ 2 P` and therefore admits an orthogonal projection.

The square-integrability data `hX : ∀ s, MemLp (X s) 2 P` is threaded as an explicit argument so
that `(X s).toLp = (hX s).toLp` is a genuine element of `Lp ℝ 2 P`. -/
noncomputable def pastSpan (X : ℤ → Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (hX : ∀ s, MemLp (X s) 2 P) (t : ℤ) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ
    (insert (oneLp P) {y : Lp ℝ 2 P | ∃ s ≤ t, y = (hX s).toLp})).topologicalClosure

variable {X : ℤ → Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P] {hX : ∀ s, MemLp (X s) 2 P}

/-- The past subspace is closed. -/
theorem isClosed_pastSpan (t : ℤ) :
    IsClosed (↑(pastSpan X P hX t) : Set (Lp ℝ 2 P)) :=
  Submodule.isClosed_topologicalClosure _

/-- The past subspace admits an orthogonal projection (it is a closed subspace of the complete
space `Lp ℝ 2 P`). -/
instance instHasOrthogonalProjectionPastSpan (t : ℤ) :
    (pastSpan X P hX t).HasOrthogonalProjection :=
  haveI : CompleteSpace (pastSpan X P hX t) :=
    (isClosed_pastSpan t).completeSpace_coe
  inferInstance

/-- The constant `1` lies in the past subspace. -/
theorem oneLp_mem_pastSpan (t : ℤ) : oneLp P ∈ pastSpan X P hX t :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_insert _ _))

/-- For `s ≤ t`, the value `(X s).toLp` lies in the time-`t` past subspace. -/
theorem toLp_mem_pastSpan {s t : ℤ} (hst : s ≤ t) : (hX s).toLp ∈ pastSpan X P hX t :=
  Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨s, hst, rfl⟩))

/-- **The past subspaces are monotone in time**: `pastSpan X P hX s ≤ pastSpan X P hX t` for
`s ≤ t`. -/
theorem pastSpan_mono {s t : ℤ} (hst : s ≤ t) :
    pastSpan X P hX s ≤ pastSpan X P hX t := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  apply Set.insert_subset_insert
  rintro y ⟨r, hr, rfl⟩
  exact ⟨r, hr.trans hst, rfl⟩

/-- **The linear predictor** onto the time-`t` past: the orthogonal projection CLM onto
`pastSpan X P hX t`. -/
noncomputable def linPred (X : ℤ → Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (hX : ∀ s, MemLp (X s) 2 P) (t : ℤ) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (pastSpan X P hX t).starProjection

/-- **The one-step Wold prediction error** `e_t = X_t − linPred_{t−1}(X_t)`, the residual of `X_t`
after projecting onto the past through time `t − 1`. -/
noncomputable def woldError (X : ℤ → Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (hX : ∀ s, MemLp (X s) 2 P) (t : ℤ) : Lp ℝ 2 P :=
  (hX t).toLp - linPred X P hX (t - 1) ((hX t).toLp)

/-- **The prediction-error variance** `σ² = ‖e₀‖²`. For a probability measure this equals
`E[e₀²] = Var[e₀]`, because the error is orthogonal to the constant `1`, hence has mean zero. -/
noncomputable def projErrorVariance (X : ℤ → Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (hX : ∀ s, MemLp (X s) 2 P) : ℝ :=
  ‖woldError X P hX 0‖ ^ 2

theorem projErrorVariance_nonneg : 0 ≤ projErrorVariance X P hX :=
  sq_nonneg _

/-- **Orthogonality of the Wold error to the past.** The one-step error `e_t` is orthogonal to
every element of the time-`(t−1)` past subspace. -/
theorem woldError_inner_eq_zero_of_mem_pastSpan {t : ℤ} {g : Lp ℝ 2 P}
    (hg : g ∈ pastSpan X P hX (t - 1)) :
    inner ℝ (woldError X P hX t) g = 0 := by
  simp only [woldError, linPred]
  exact Submodule.inner_left_of_mem_orthogonal hg
    (Submodule.sub_starProjection_mem_orthogonal (K := pastSpan X P hX (t - 1)) ((hX t).toLp))

/-- **Norm minimality of the Wold error.** The error `e_t` is at least as close to the past as any
element `g` of the past subspace: `‖e_t‖ ≤ ‖X_t − g‖`. In particular no past-measurable predictor
beats the projection. -/
theorem norm_woldError_le {t : ℤ} {g : Lp ℝ 2 P} (hg : g ∈ pastSpan X P hX (t - 1)) :
    ‖woldError X P hX t‖ ≤ ‖(hX t).toLp - g‖ := by
  simp only [woldError, linPred]
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
    (⟨g, hg⟩ : pastSpan X P hX (t - 1))

/-- **The remote (distant) past** `⋂_t pastSpan(t)`: the intersection of all past subspaces.
Hansen's `µ_t` is the projection of `X_t` onto this subspace. -/
noncomputable def remotePast (X : ℤ → Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P]
    (hX : ∀ s, MemLp (X s) 2 P) : Submodule ℝ (Lp ℝ 2 P) :=
  ⨅ t : ℤ, pastSpan X P hX t

theorem remotePast_le (t : ℤ) : remotePast X P hX ≤ pastSpan X P hX t :=
  iInf_le _ t

/-- The remote past is closed. -/
theorem isClosed_remotePast :
    IsClosed (↑(remotePast X P hX) : Set (Lp ℝ 2 P)) := by
  rw [remotePast, Submodule.coe_iInf]
  exact isClosed_iInter fun t => isClosed_pastSpan t

/-- The remote past admits an orthogonal projection. -/
instance instHasOrthogonalProjectionRemotePast :
    (remotePast X P hX).HasOrthogonalProjection :=
  haveI : CompleteSpace (remotePast X P hX) := isClosed_remotePast.completeSpace_coe
  inferInstance

/-- **The anchored past family is antitone.** For fixed `t`, the subspaces
`fun m : ℕ => pastSpan X P hX (t − m)` decrease as the horizon `m` grows. This is the family fed to
`Submodule.starProjection_tendsto_iInf_of_antitone` in the Wold theorem. -/
theorem antitone_pastSpan_sub (t : ℤ) :
    Antitone fun m : ℕ => pastSpan X P hX (t - m) := by
  intro m n hmn
  exact pastSpan_mono (by exact_mod_cast Int.sub_le_sub_left (by exact_mod_cast hmn) t)

/-- **The anchored remote past is the remote past.** For any anchor `t`, the intersection of the
past subspaces along the receding horizon `t − m` (`m : ℕ`) equals the remote past. This lets the
Wold theorem read off `remotePast` as the limit subspace of the antitone family
`fun m => pastSpan X P hX (t − m)`. -/
theorem iInf_pastSpan_sub (t : ℤ) :
    ⨅ m : ℕ, pastSpan X P hX (t - m) = remotePast X P hX := by
  refine le_antisymm (le_iInf fun s => ?_) (le_iInf fun m => iInf_le _ (t - m))
  rcases le_or_gt s t with hs | hs
  · have hm : t - ((t - s).toNat : ℤ) = s := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    calc ⨅ m : ℕ, pastSpan X P hX (t - m)
        ≤ pastSpan X P hX (t - ((t - s).toNat : ℤ)) := iInf_le _ _
      _ = pastSpan X P hX s := by rw [hm]
  · calc ⨅ m : ℕ, pastSpan X P hX (t - m)
        ≤ pastSpan X P hX (t - ((0 : ℕ) : ℤ)) := iInf_le _ 0
      _ = pastSpan X P hX t := by rw [Nat.cast_zero, sub_zero]
      _ ≤ pastSpan X P hX s := pastSpan_mono hs.le

/-- **Convergence of the linear predictor to the remote-past projection.** For a fixed anchor `t`,
the orthogonal projections of `x` onto the receding pasts `pastSpan X P hX (t − m)` converge, as the
horizon `m → ∞`, to the projection of `x` onto the remote past. This packages
`starProjection_tendsto_iInf_of_antitone` for the process family, and is the limit
`µ_t = lim_{m→∞} P_{t−m}[X_t]` used by the Wold theorem (14.17). -/
theorem tendsto_starProjection_pastSpan_sub (t : ℤ) (x : Lp ℝ 2 P) :
    Tendsto (fun m : ℕ => (pastSpan X P hX (t - m)).starProjection x) atTop
      (𝓝 ((remotePast X P hX).starProjection x)) := by
  haveI : (⨅ m : ℕ, pastSpan X P hX (t - m)).HasOrthogonalProjection := by
    rw [iInf_pastSpan_sub]; infer_instance
  have hlim := Submodule.starProjection_tendsto_iInf_of_antitone
    (U := fun m : ℕ => pastSpan X P hX (t - m)) (antitone_pastSpan_sub t) x
  have heq : ⨅ m : ℕ, pastSpan X P hX (t - m) = remotePast X P hX := iInf_pastSpan_sub t
  have hpoint : (⨅ m : ℕ, pastSpan X P hX (t - m)).starProjection x
      = (remotePast X P hX).starProjection x := by
    refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
    · rw [← heq]; exact Submodule.starProjection_apply_mem _ x
    · rw [← heq]
      exact Submodule.sub_starProjection_mem_orthogonal
        (K := ⨅ m : ℕ, pastSpan X P hX (t - m)) x
  rwa [hpoint] at hlim

/-! ### Hansen Theorem 14.16 — the projection equation on the original space

The next two results hold for any square-integrable process `X : ℤ → Ω → ℝ` on the finite measure
space `(Ω, P)` and do not need stationarity: the Wold error has mean zero and is serially
uncorrelated. -/

/-- The time-`t` linear predictor lands in the time-`t` past subspace: `linPred_t x ∈ pastSpan_t`.
This is the defining membership of the orthogonal projection; it puts `woldError (t − j)` inside
`pastSpan (t − 1)` in the serial-uncorrelatedness argument. -/
theorem linPred_mem_pastSpan (t : ℤ) (x : Lp ℝ 2 P) :
    linPred X P hX t x ∈ pastSpan X P hX t :=
  Submodule.starProjection_apply_mem _ x

/-- Inner product against the constant `1` is the integral: `⟪f, 1⟫ = ∫ f ∂P`. -/
private theorem inner_oneLp_eq_integral (f : Lp ℝ 2 P) :
    inner ℝ f (oneLp P) = ∫ ω, f ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  have hone : (⇑(oneLp P) : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _
  filter_upwards [hone] with a ha
  rw [ha]
  simp [real_inner_eq_re_inner, RCLike.inner_apply]

/-- **Hansen Theorem 14.16 (mean zero).** The one-step Wold error integrates to zero, because it is
orthogonal to the constant `1 ∈ pastSpan (t − 1)`. For a probability measure this is `E[e_t] = 0`.
-/
theorem integral_woldError_eq_zero (t : ℤ) :
    ∫ ω, woldError X P hX t ω ∂P = 0 := by
  rw [← inner_oneLp_eq_integral (woldError X P hX t)]
  exact woldError_inner_eq_zero_of_mem_pastSpan (oneLp_mem_pastSpan (t - 1))

/-- **Hansen Theorem 14.16 (serial uncorrelatedness).** For every lag `j ≥ 1` the Wold errors at
times `t` and `t − j` are orthogonal in `Lp ℝ 2 P`: `⟪e_t, e_{t−j}⟫ = 0`. Since each error has mean
zero (`integral_woldError_eq_zero`), this is exactly the white-noise autocovariance `γ_e(j) = 0`.

The mechanism is that `e_{t−j}` is built from `X_{t−j}` and a projection onto `pastSpan (t−j−1)`,
both of which sit inside `pastSpan (t − 1)` when `j ≥ 1`, and `e_t` is orthogonal to that past. -/
theorem inner_woldError_woldError_eq_zero {t j : ℤ} (hj : 1 ≤ j) :
    inner ℝ (woldError X P hX t) (woldError X P hX (t - j)) = 0 := by
  apply woldError_inner_eq_zero_of_mem_pastSpan
  simp only [woldError, linPred]
  refine Submodule.sub_mem _ (toLp_mem_pastSpan (by omega)) ?_
  refine pastSpan_mono (show (t - j) - 1 ≤ t - 1 by omega) ?_
  exact Submodule.starProjection_apply_mem _ _

/-! ### The lag isometry on path space and stationary error variance

The stationarity half of Theorem 14.16 — that the prediction-error variance does not depend on the
time index — is delivered by the lag operator on `Lp ℝ 2 (pathLaw X P)`. It is stated for the
coordinate process `pathCoord` on path space, where the shift is genuinely measure preserving. -/

/-- The canonical **coordinate process** on path space `ℤ → ℝ`: `pathCoord t x = x t`. Under
`pathLaw X P` this reads off the process `X`, and it is the process the lag isometry acts on. -/
def pathCoord : ℤ → (ℤ → ℝ) → ℝ := fun t x => x t

theorem measurable_pathCoord (s : ℤ) : Measurable (pathCoord s) :=
  measurable_pi_apply s

/-- The push-forward of a finite measure is finite, so the path law is a finite measure; this makes
`oneLp` and `pastSpan` available on `Lp ℝ 2 (pathLaw X P)`. -/
instance instIsFiniteMeasurePathLaw : IsFiniteMeasure (pathLaw X P) :=
  P.isFiniteMeasure_map _

omit [IsFiniteMeasure P] in
/-- The coordinate process is square-integrable under the path law, from square-integrability of the
underlying process `X`. This supplies the `MemLp` data needed to build `pastSpan` for `pathCoord`.
-/
theorem memLp_pathCoord_pathLaw (hmeas : ∀ t, AEMeasurable (X t) P)
    (hX2 : ∀ s, MemLp (X s) 2 P) (s : ℤ) :
    MemLp (pathCoord s) 2 (pathLaw X P) :=
  (memLp_map_measure_iff (measurable_pathCoord s).aestronglyMeasurable
    (aemeasurable_pi_iff.mpr hmeas)).mpr (hX2 s)

/-- Composition with a measure-preserving map that is the identity acts trivially on `Lp`. This is
the workhorse behind the two inverse identities of `lagIsometryL2`; it abstracts the map so that the
identity substitution is clean (the measure-preservation proof is discharged by proof irrelevance).
-/
private theorem compMeasurePreserving_eq_self_of_eq_id {μ' : Measure (ℤ → ℝ)}
    (F : (ℤ → ℝ) → (ℤ → ℝ)) (hF : MeasurePreserving F μ' μ') (hid : F = id)
    (x : Lp ℝ 2 μ') : Lp.compMeasurePreserving F hF x = x := by
  subst hid
  exact Lp.compMeasurePreserving_id_apply x

/-- Equal subspaces have equal orthogonal projections. The `HasOrthogonalProjection` instances are
`Prop`s, so once the subspaces coincide the projection maps agree by proof irrelevance. This lets us
transport a projection along `lagIsometry_map_pastSpan` without a dependent rewrite. -/
private theorem starProjection_congr {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {A B : Submodule ℝ F} [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    (h : A = B) (x : F) : A.starProjection x = B.starProjection x := by
  subst h
  rfl

/-- **The lag isometry.** For a strictly stationary process, composition with the coordinate shift
`pathShift ℝ` is a surjective linear isometry of `Lp ℝ 2 (pathLaw X P)` — the L² lag operator. It is
built from the forward composition `Lp.compMeasurePreservingₗᵢ` and its measure-preserving inverse
(composition with `(pathShiftEquiv ℝ).symm`), which are mutual inverses since the two shifts cancel.
This is the stationarity engine for Hansen Theorems 14.16 and 14.17. -/
noncomputable def lagIsometryL2 (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) :
    Lp ℝ 2 (pathLaw X P) ≃ₗᵢ[ℝ] Lp ℝ 2 (pathLaw X P) :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℝ (pathShift ℝ) (hSS.measurePreserving_pathShift hmeas))
    (Lp.compMeasurePreservingₗ ℝ (⇑(pathShiftEquiv ℝ).symm)
      (MeasurePreserving.symm (pathShiftEquiv ℝ) (hSS.measurePreserving_pathShift hmeas)))
    (by
      refine LinearMap.ext fun x => ?_
      change Lp.compMeasurePreserving (pathShift ℝ) (hSS.measurePreserving_pathShift hmeas)
          (Lp.compMeasurePreserving (⇑(pathShiftEquiv ℝ).symm)
            (MeasurePreserving.symm (pathShiftEquiv ℝ)
              (hSS.measurePreserving_pathShift hmeas)) x) = x
      rw [← Lp.compMeasurePreserving_comp_apply]
      refine compMeasurePreserving_eq_self_of_eq_id _ _ ?_ x
      funext y
      exact (pathShiftEquiv ℝ).symm_apply_apply y)
    (by
      refine LinearMap.ext fun x => ?_
      change Lp.compMeasurePreserving (⇑(pathShiftEquiv ℝ).symm)
          (MeasurePreserving.symm (pathShiftEquiv ℝ) (hSS.measurePreserving_pathShift hmeas))
          (Lp.compMeasurePreserving (pathShift ℝ) (hSS.measurePreserving_pathShift hmeas) x) = x
      rw [← Lp.compMeasurePreserving_comp_apply]
      refine compMeasurePreserving_eq_self_of_eq_id _ _ ?_ x
      funext y
      exact (pathShiftEquiv ℝ).apply_symm_apply y)

/-- The lag isometry advances the coordinate index by one: `L (X_s) = X_{s+1}` in `Lp`. -/
theorem lagIsometryL2_apply_toLp (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (s : ℤ) :
    lagIsometryL2 hSS hmeas ((hE s).toLp) = (hE (s + 1)).toLp := by
  change Lp.compMeasurePreserving (pathShift ℝ) (hSS.measurePreserving_pathShift hmeas)
      ((hE s).toLp) = (hE (s + 1)).toLp
  rw [Lp.toLp_compMeasurePreserving]
  rfl

/-- The lag isometry fixes the intercept: `L 1 = 1`. -/
theorem lagIsometryL2_apply_oneLp (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) :
    lagIsometryL2 hSS hmeas (oneLp (pathLaw X P)) = oneLp (pathLaw X P) := by
  simp only [oneLp]
  change Lp.compMeasurePreserving (pathShift ℝ) (hSS.measurePreserving_pathShift hmeas)
      (MemLp.toLp (fun _ => (1 : ℝ)) (memLp_const 1))
    = MemLp.toLp (fun _ => (1 : ℝ)) (memLp_const 1)
  rw [Lp.toLp_compMeasurePreserving]
  rfl

/-- **The lag isometry shifts the past.** It carries the time-`t` past subspace onto the
time-`(t+1)` past subspace, `L (pastSpan_t) = pastSpan_{t+1}`. This is the geometric content that
transports the one-step prediction problem forward by one period. -/
theorem lagIsometry_map_pastSpan (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (t : ℤ) :
    (pastSpan pathCoord (pathLaw X P) hE t).map
        (lagIsometryL2 hSS hmeas).toLinearIsometry.toLinearMap
      = pastSpan pathCoord (pathLaw X P) hE (t + 1) := by
  set L := lagIsometryL2 hSS hmeas with hL
  set Lm := L.toLinearIsometry.toLinearMap with hLm
  -- The isometry, being a homeomorphism, commutes `Submodule.map` with `topologicalClosure`.
  have hcoe : ⇑Lm = ⇑L.toHomeomorph := by
    simp only [hLm, LinearIsometry.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.coe_toHomeomorph]
  have hclosuremap : ∀ K : Submodule ℝ (Lp ℝ 2 (pathLaw X P)),
      (K.topologicalClosure).map Lm = (K.map Lm).topologicalClosure := by
    intro K
    refine SetLike.coe_injective ?_
    simp only [Submodule.map_coe, Submodule.topologicalClosure_coe, hcoe]
    exact (L.toHomeomorph.isClosedMap.closure_image_eq_of_continuous
      L.toHomeomorph.continuous _).symm
  -- The generating set is carried onto the shifted generating set.
  have himg : (⇑Lm) '' (insert (oneLp (pathLaw X P))
        {y : Lp ℝ 2 (pathLaw X P) | ∃ s ≤ t, y = (hE s).toLp})
      = insert (oneLp (pathLaw X P))
        {y : Lp ℝ 2 (pathLaw X P) | ∃ s ≤ t + 1, y = (hE s).toLp} := by
    rw [Set.image_insert_eq]
    refine congrArg₂ _ ?_ ?_
    · change L (oneLp (pathLaw X P)) = oneLp (pathLaw X P)
      exact lagIsometryL2_apply_oneLp hSS hmeas
    · ext z
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s + 1, by omega, lagIsometryL2_apply_toLp hSS hmeas hE s⟩
      · rintro ⟨r, hr, rfl⟩
        refine ⟨(hE (r - 1)).toLp, ⟨r - 1, by omega, rfl⟩, ?_⟩
        have hz := lagIsometryL2_apply_toLp hSS hmeas hE (r - 1)
        rw [show (r - 1) + 1 = r by ring] at hz
        exact hz
  have hspan : (Submodule.span ℝ (insert (oneLp (pathLaw X P))
        {y : Lp ℝ 2 (pathLaw X P) | ∃ s ≤ t, y = (hE s).toLp})).map Lm
      = Submodule.span ℝ (insert (oneLp (pathLaw X P))
        {y : Lp ℝ 2 (pathLaw X P) | ∃ s ≤ t + 1, y = (hE s).toLp}) := by
    rw [Submodule.map_span, himg]
  simp only [pastSpan]
  rw [hclosuremap, hspan]

/-- **The lag isometry moves the Wold error forward one period**: `L (e_t) = e_{t+1}`. The intercept
and coordinate parts move by `lagIsometryL2_apply_oneLp` / `lagIsometryL2_apply_toLp`, and the
projection part by `LinearIsometry.map_starProjection` together with `lagIsometry_map_pastSpan`. -/
theorem lagIsometry_woldError (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (t : ℤ) :
    lagIsometryL2 hSS hmeas (woldError pathCoord (pathLaw X P) hE t)
      = woldError pathCoord (pathLaw X P) hE (t + 1) := by
  haveI hHOP : ((pastSpan pathCoord (pathLaw X P) hE (t - 1)).map
      (lagIsometryL2 hSS hmeas).toLinearIsometry.toLinearMap).HasOrthogonalProjection := by
    rw [lagIsometry_map_pastSpan hSS hmeas hE (t - 1)]
    infer_instance
  have hmapeq : (pastSpan pathCoord (pathLaw X P) hE (t - 1)).map
        (lagIsometryL2 hSS hmeas).toLinearIsometry.toLinearMap
      = pastSpan pathCoord (pathLaw X P) hE t := by
    rw [lagIsometry_map_pastSpan hSS hmeas hE (t - 1), show (t - 1) + 1 = t by ring]
  have hproj : lagIsometryL2 hSS hmeas
        ((pastSpan pathCoord (pathLaw X P) hE (t - 1)).starProjection ((hE t).toLp))
      = (pastSpan pathCoord (pathLaw X P) hE t).starProjection ((hE (t + 1)).toLp) := by
    have hms := LinearIsometry.map_starProjection (lagIsometryL2 hSS hmeas).toLinearIsometry
      (pastSpan pathCoord (pathLaw X P) hE (t - 1)) ((hE t).toLp)
    rw [starProjection_congr hmapeq, LinearIsometryEquiv.coe_toLinearIsometry,
      lagIsometryL2_apply_toLp hSS hmeas hE t] at hms
    exact hms
  simp only [woldError, linPred, map_sub]
  rw [lagIsometryL2_apply_toLp hSS hmeas hE t, hproj, show (t + 1) - 1 = t by ring]

/-- The prediction-error norm is the same at every time: `‖e_t‖ = ‖e_0‖`. This is the stationarity
of the innovation variance, proved by pushing the equal-norm relation `‖e_{t+1}‖ = ‖e_t‖` (from the
lag isometry) up and down the integers. -/
theorem norm_woldError_pathCoord_eq (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (t : ℤ) :
    ‖woldError pathCoord (pathLaw X P) hE t‖ = ‖woldError pathCoord (pathLaw X P) hE 0‖ := by
  have hsucc : ∀ s : ℤ, ‖woldError pathCoord (pathLaw X P) hE (s + 1)‖
      = ‖woldError pathCoord (pathLaw X P) hE s‖ := by
    intro s
    rw [← lagIsometry_woldError hSS hmeas hE s]
    exact (lagIsometryL2 hSS hmeas).norm_map _
  induction t using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [hsucc]; exact ih
  | pred i ih =>
    have h := hsucc (-(i : ℤ) - 1)
    rw [show (-(i : ℤ) - 1) + 1 = -(i : ℤ) by ring] at h
    rw [← h]; exact ih

/-- **Hansen Theorem 14.16 (stationary innovation variance).** The squared prediction-error norm
equals the prediction-error variance `σ²` at every time index. For a strictly stationary process the
innovation variance `E[e_t²]` does not depend on `t`. -/
theorem variance_woldError_pathCoord (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (t : ℤ) :
    ‖woldError pathCoord (pathLaw X P) hE t‖ ^ 2
      = projErrorVariance pathCoord (pathLaw X P) hE := by
  unfold projErrorVariance
  rw [norm_woldError_pathCoord_eq hSS hmeas hE t]

/-! ### Hansen Theorem 14.17 — the Wold decomposition

We now assemble the Wold decomposition proper. The construction is run on the coordinate process
`pathCoord` over `Lp ℝ 2 (pathLaw X P)`, where the innovation variance is stationary
(`variance_woldError_pathCoord`). The heart is a projection-tower induction expressing the linear
predictor `P_{t−m}[Y_t]` as `Y_t` minus a partial Wold sum; letting `m → ∞` and identifying the
limit with the remote-past projection yields `Y_t = µ_t + ∑_j b_j e_{t−j}`. -/

/-- The one-step Wold error `e_s` lies in the time-`s` past subspace `pastSpan s`. Indeed
`e_s = X_s − linPred_{s−1}(X_s)`, and both `X_s` (as `s ≤ s`) and the predictor (which sits in the
smaller `pastSpan (s−1)`) belong to `pastSpan s`. -/
theorem woldError_mem_pastSpan (s : ℤ) : woldError X P hX s ∈ pastSpan X P hX s := by
  refine Submodule.sub_mem _ (toLp_mem_pastSpan le_rfl) ?_
  exact pastSpan_mono (by omega) (linPred_mem_pastSpan (s - 1) ((hX s).toLp))

/-- **Orthogonality to the past from orthogonality to its generators.** If `y` is orthogonal to the
intercept `1` and to every value `X_r` with `r ≤ t`, then it is orthogonal to the whole closed span
`pastSpan t`. The singleton complement `(ℝ ∙ y)ᗮ` is closed and contains all the generators, so it
contains their closed span. -/
private theorem mem_orthogonal_pastSpan_of_generators {y : Lp ℝ 2 P} {t : ℤ}
    (h1 : inner ℝ y (oneLp P) = 0) (h2 : ∀ r ≤ t, inner ℝ y ((hX r).toLp) = 0) :
    y ∈ (pastSpan X P hX t)ᗮ := by
  have hle : pastSpan X P hX t ≤ (ℝ ∙ y)ᗮ := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_setOf_eq] at hz
      obtain rfl | ⟨r, hr, rfl⟩ := hz
      · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr h1
      · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (h2 r hr)
    · exact Submodule.isClosed_orthogonal _
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hyu := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hu)
  rwa [real_inner_comm] at hyu

/-- **The one-step innovation projection.** Projecting `x` onto `pastSpan s` differs from projecting
onto the smaller `pastSpan (s−1)` by the rank-one component along the innovation `e_s`:
`P_s x = P_{s−1} x + (⟪e_s, x⟫ / ‖e_s‖²) • e_s`. This is the atomic step of the Wold projection
tower: `pastSpan s` decomposes as `pastSpan (s−1)` plus the innovation line `ℝ ∙ e_s`. Holds for any
square-integrable process (no stationarity needed). -/
theorem starProjection_pastSpan_pred (s : ℤ) (x : Lp ℝ 2 P) :
    (pastSpan X P hX s).starProjection x
      = (pastSpan X P hX (s - 1)).starProjection x
        + (inner ℝ (woldError X P hX s) x / ‖woldError X P hX s‖ ^ 2) • woldError X P hX s := by
  have hesplit : (hX s).toLp
      = woldError X P hX s + (pastSpan X P hX (s - 1)).starProjection ((hX s).toLp) := by
    have h : woldError X P hX s
        = (hX s).toLp - (pastSpan X P hX (s - 1)).starProjection ((hX s).toLp) := rfl
    rw [h]; abel
  set e := woldError X P hX s with he_def
  set K := pastSpan X P hX (s - 1) with hK_def
  set c : ℝ := inner ℝ e x / ‖e‖ ^ 2 with hc_def
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · -- membership `P_{s−1} x + c • e ∈ pastSpan s`
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (woldError_mem_pastSpan s))
    exact pastSpan_mono (by omega) (Submodule.starProjection_apply_mem K x)
  · -- orthogonality of the residual to `pastSpan s`
    -- the residual is orthogonal to every element of `K = pastSpan (s−1)`
    have hgen : ∀ g ∈ K, inner ℝ (x - (K.starProjection x + c • e)) g = 0 := by
      intro g hg
      have h1 : inner ℝ (x - K.starProjection x) g = 0 :=
        Submodule.inner_left_of_mem_orthogonal hg (Submodule.sub_starProjection_mem_orthogonal x)
      have h2 : inner ℝ e g = 0 := woldError_inner_eq_zero_of_mem_pastSpan hg
      have hexp : inner ℝ (x - (K.starProjection x + c • e)) g
          = inner ℝ (x - K.starProjection x) g - c * inner ℝ e g := by
        simp only [inner_sub_left, inner_add_left, real_inner_smul_left]; ring
      rw [hexp, h1, h2]; ring
    -- and orthogonal to the innovation `e` itself
    have hye : inner ℝ (x - (K.starProjection x + c • e)) e = 0 := by
      by_cases he0 : e = 0
      · rw [he0, inner_zero_right]
      · have hnorm : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he0)
        have hKe : inner ℝ (K.starProjection x) e = 0 := by
          rw [real_inner_comm]
          exact woldError_inner_eq_zero_of_mem_pastSpan (Submodule.starProjection_apply_mem K x)
        have hce : c * ‖e‖ ^ 2 = inner ℝ e x := by
          rw [hc_def, div_mul_cancel₀ _ hnorm]
        simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hKe,
          real_inner_self_eq_norm_sq]
        rw [← real_inner_comm x e, hce]; ring
    apply mem_orthogonal_pastSpan_of_generators
    · exact hgen _ (oneLp_mem_pastSpan (s - 1))
    · intro r hr
      rcases lt_or_eq_of_le hr with hlt | rfl
      · exact hgen _ (toLp_mem_pastSpan (by omega))
      · rw [hesplit, inner_add_right, hye, hgen _ (Submodule.starProjection_apply_mem K _)]; ring

/-- **Time-invariance of the Wold cross-moments.** For the stationary coordinate process, the inner
product `⟪e_{t−k}, Y_t⟫` between the innovation at lag `k` and the current value does not depend on
the anchor `t`: the lag isometry moves both arguments forward by one period and preserves inner
products. This is what makes the Wold coefficients time-independent. -/
theorem inner_woldError_toLp_eq (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (k t : ℤ) :
    inner ℝ (woldError pathCoord (pathLaw X P) hE (t - k)) ((hE t).toLp)
      = inner ℝ (woldError pathCoord (pathLaw X P) hE (0 - k)) ((hE 0).toLp) := by
  have hshift : ∀ s : ℤ,
      inner ℝ (woldError pathCoord (pathLaw X P) hE (s + 1 - k)) ((hE (s + 1)).toLp)
        = inner ℝ (woldError pathCoord (pathLaw X P) hE (s - k)) ((hE s).toLp) := by
    intro s
    rw [show s + 1 - k = (s - k) + 1 from by ring, ← lagIsometry_woldError hSS hmeas hE (s - k),
        ← lagIsometryL2_apply_toLp hSS hmeas hE s, LinearIsometryEquiv.inner_map_map]
  induction t using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [hshift]; exact ih
  | pred i ih =>
    have h := hshift (-(i : ℤ) - 1)
    rw [show (-(i : ℤ) - 1) + 1 = -(i : ℤ) by ring] at h
    rw [← h]; exact ih

/-- **The Wold coefficients** `b_j = ⟪e_{−j}, Y_0⟫ / σ²`, anchored at time `0`. By
`inner_woldError_toLp_eq` and variance stationarity these coincide with `⟪e_{t−j}, Y_t⟫ / σ²` at
every anchor `t` (`woldCoeff_eq`), which is Hansen's `b_j`. The normalisation `b_0 = 1`
(`woldCoeff_zero`) reflects `Y_t − e_t ⟂ e_t`. -/
noncomputable def woldCoeff (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (j : ℕ) : ℝ :=
  inner ℝ (woldError pathCoord (pathLaw X P) hE (0 - (j : ℤ))) ((hE 0).toLp)
    / projErrorVariance pathCoord (pathLaw X P) hE

/-- **The Wold coefficient at any anchor.** `⟪e_{t−j}, Y_t⟫ / ‖e_{t−j}‖² = b_j`: the lag-`j`
regression coefficient of `Y_t` on the innovation `e_{t−j}` is the anchored coefficient
`woldCoeff j`, independent of `t`. Combines time-invariance of the cross-moment with variance
stationarity. -/
theorem woldCoeff_eq (hSS : IsStrictlyStationary X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (t : ℤ) (j : ℕ) :
    inner ℝ (woldError pathCoord (pathLaw X P) hE (t - j)) ((hE t).toLp)
        / ‖woldError pathCoord (pathLaw X P) hE (t - j)‖ ^ 2
      = woldCoeff hE j := by
  unfold woldCoeff
  rw [variance_woldError_pathCoord hSS hmeas hE (t - j),
    inner_woldError_toLp_eq hSS hmeas hE (j : ℤ) t]

/-- **The leading Wold coefficient is one.** `b_0 = 1`, because `Y_0 = e_0 + P_{−1}[Y_0]` with
`P_{−1}[Y_0] ⟂ e_0`, so `⟪e_0, Y_0⟫ = ‖e_0‖² = σ²`. Needs a non-degenerate innovation (`σ² > 0`). -/
theorem woldCoeff_zero (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) hE) :
    woldCoeff hE 0 = 1 := by
  have hsplit : ((hE 0).toLp : Lp ℝ 2 (pathLaw X P))
      = woldError pathCoord (pathLaw X P) hE 0
        + (pastSpan pathCoord (pathLaw X P) hE (0 - 1)).starProjection ((hE 0).toLp) := by
    have h : woldError pathCoord (pathLaw X P) hE 0
        = (hE 0).toLp
          - (pastSpan pathCoord (pathLaw X P) hE (0 - 1)).starProjection ((hE 0).toLp) := rfl
    rw [h]; abel
  have hnum : inner ℝ (woldError pathCoord (pathLaw X P) hE 0) ((hE 0).toLp)
      = projErrorVariance pathCoord (pathLaw X P) hE := by
    rw [hsplit, inner_add_right, real_inner_self_eq_norm_sq,
        woldError_inner_eq_zero_of_mem_pastSpan (Submodule.starProjection_apply_mem _ _), add_zero]
    rfl
  unfold woldCoeff
  rw [show (0 : ℤ) - ((0 : ℕ) : ℤ) = 0 by norm_num, hnum, div_self (ne_of_gt hσ)]

/-- **The Wold projection tower.** Iterating the one-step innovation projection, the linear
predictor of `Y_t` on the horizon-`m` past equals `Y_t` minus the leading `m` terms of the Wold
series: `P_{t−m}[Y_t] = Y_t − ∑_{j<m} b_j e_{t−j}`. Proved by induction on `m`; the step peels off
the lag-`m` innovation via `starProjection_pastSpan_pred`, with its coefficient identified as `b_m`
by `woldCoeff_eq`. -/
theorem starProjection_pastSpan_sub_eq (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (t : ℤ) (m : ℕ) :
    (pastSpan pathCoord (pathLaw X P) hE (t - m)).starProjection ((hE t).toLp)
      = (hE t).toLp
        - ∑ j ∈ Finset.range m, woldCoeff hE j • woldError pathCoord (pathLaw X P) hE (t - j) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, sub_zero, Finset.range_zero, Finset.sum_empty]
    exact Submodule.starProjection_eq_self_iff.mpr (toLp_mem_pastSpan le_rfl)
  | succ m ih =>
    have hstep := starProjection_pastSpan_pred (X := pathCoord) (P := pathLaw X P) (hX := hE)
      (t - m) ((hE t).toLp)
    rw [woldCoeff_eq hSS hmeas hE t m] at hstep
    have hstep' := eq_sub_of_add_eq hstep.symm
    have hidx : t - ((m + 1 : ℕ) : ℤ) = t - (m : ℤ) - 1 := by push_cast; ring
    rw [hidx, hstep', ih, Finset.sum_range_succ]
    abel

/-- **Serial orthogonality of the innovations along a receding horizon.** For `i ≠ j` the
innovations `e_{t−i}` and `e_{t−j}` are orthogonal, from the white-noise property
`inner_woldError_woldError_eq_zero`. -/
private theorem inner_woldError_sub_eq_zero (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (t : ℤ)
    {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (woldError pathCoord (pathLaw X P) hE (t - i))
        (woldError pathCoord (pathLaw X P) hE (t - j)) = 0 := by
  have key : ∀ a b : ℕ, a < b →
      inner ℝ (woldError pathCoord (pathLaw X P) hE (t - a))
        (woldError pathCoord (pathLaw X P) hE (t - b)) = 0 := by
    intro a b hab
    have h := inner_woldError_woldError_eq_zero (X := pathCoord) (P := pathLaw X P) (hX := hE)
      (t := t - a) (j := (b : ℤ) - a) (by omega)
    rwa [show (t - (a : ℤ)) - ((b : ℤ) - a) = t - b from by ring] at h
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · rw [real_inner_comm]; exact key j i h

/-- **The normalised innovation family is orthonormal.** Rescaling each innovation `e_{t−j}` by
`σ⁻¹` yields an orthonormal sequence in `Lp ℝ 2 (pathLaw X P)`: unit norm from variance stationarity
and non-degeneracy `σ² > 0`, and pairwise orthogonality from serial uncorrelatedness. This is the
frame that makes the Wold series a genuine (Bessel-summable) orthogonal expansion. -/
theorem orthonormal_woldError_smul (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) hE) (t : ℤ) :
    Orthonormal ℝ (fun j : ℕ =>
      (Real.sqrt (projErrorVariance pathCoord (pathLaw X P) hE))⁻¹
        • woldError pathCoord (pathLaw X P) hE (t - j)) := by
  have hsq_pos : 0 < Real.sqrt (projErrorVariance pathCoord (pathLaw X P) hE) :=
    Real.sqrt_pos.mpr hσ
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · have hnorme : ‖woldError pathCoord (pathLaw X P) hE (t - j)‖
        = Real.sqrt (projErrorVariance pathCoord (pathLaw X P) hE) := by
      rw [← variance_woldError_pathCoord hSS hmeas hE (t - j), Real.sqrt_sq (norm_nonneg _)]
    rw [norm_smul, hnorme, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hsq_pos.le),
      inv_mul_cancel₀ (ne_of_gt hsq_pos)]
  · dsimp only
    rw [real_inner_smul_left, real_inner_smul_right, inner_woldError_sub_eq_zero hE t hij,
      mul_zero, mul_zero]

/-- **Bessel's inequality for the Wold coefficients.** `∑_j b_j²` converges. The partial sums equal
`σ⁻² ‖∑_{j<m} b_j e_{−j}‖²` (Pythagoras over the orthonormal frame), and that sum is
`Y₀ − P_{−m}[Y₀]`, a projection residual of norm at most `‖Y₀‖`; so the partial sums are bounded by
`‖Y₀‖² / σ²`. -/
theorem summable_sq_woldCoeff (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) hE) :
    Summable (fun j => (woldCoeff hE j) ^ 2) := by
  have hv := orthonormal_woldError_smul hSS hmeas hE hσ 0
  set σ2 := projErrorVariance pathCoord (pathLaw X P) hE with hσ2def
  set sq := Real.sqrt σ2 with hsqdef
  have hsq_pos : 0 < sq := Real.sqrt_pos.mpr hσ
  have hsq2 : sq ^ 2 = σ2 := Real.sq_sqrt hσ.le
  have hof := hv.orthogonalFamily
  set V := fun j : ℕ => LinearIsometry.toSpanSingleton ℝ (Lp ℝ 2 (pathLaw X P)) (hv.1 j) with hVdef
  have hVeq : ∀ j, V j (woldCoeff hE j * sq)
      = woldCoeff hE j • woldError pathCoord (pathLaw X P) hE ((0 : ℤ) - j) := by
    intro j
    simp only [hVdef, LinearIsometry.toSpanSingleton_apply, smul_smul, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hsq_pos), mul_one]
  refine summable_of_sum_range_le (c := ‖(hE 0).toLp‖ ^ 2 / σ2) (fun n => sq_nonneg _) (fun m => ?_)
  -- Pythagoras identity over the orthonormal frame
  have hns := hof.norm_sum (fun j => woldCoeff hE j * sq) (Finset.range m)
  have hSeq : ∑ j ∈ Finset.range m, V j (woldCoeff hE j * sq)
      = ∑ j ∈ Finset.range m,
          woldCoeff hE j • woldError pathCoord (pathLaw X P) hE ((0 : ℤ) - j) :=
    Finset.sum_congr rfl (fun j _ => hVeq j)
  rw [hSeq] at hns
  -- the partial Wold sum is the projection residual of `Y₀`
  have hSval : ∑ j ∈ Finset.range m,
        woldCoeff hE j • woldError pathCoord (pathLaw X P) hE ((0 : ℤ) - j)
      = (pastSpan pathCoord (pathLaw X P) hE (0 - m))ᗮ.starProjection ((hE 0).toLp) := by
    rw [Submodule.starProjection_orthogonal_val, starProjection_pastSpan_sub_eq hSS hmeas hE 0 m]
    abel
  -- bound its norm by `‖Y₀‖`
  have hnorm_le : ‖∑ j ∈ Finset.range m,
      woldCoeff hE j • woldError pathCoord (pathLaw X P) hE ((0 : ℤ) - j)‖ ≤ ‖(hE 0).toLp‖ := by
    rw [hSval]
    exact Submodule.norm_starProjection_apply_le
      (K := (pastSpan pathCoord (pathLaw X P) hE (0 - m))ᗮ) ((hE 0).toLp)
  -- convert the RHS of `hns` into `(∑ b_j²) · σ²`
  have hrhs : ∑ j ∈ Finset.range m, ‖woldCoeff hE j * sq‖ ^ 2
      = (∑ j ∈ Finset.range m, (woldCoeff hE j) ^ 2) * σ2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, mul_pow, hsq2]
  rw [hrhs] at hns
  -- assemble: (∑ b_j²)·σ² = ‖residual‖² ≤ ‖Y₀‖²
  have hle : (∑ j ∈ Finset.range m, (woldCoeff hE j) ^ 2) * σ2 ≤ ‖(hE 0).toLp‖ ^ 2 := by
    rw [← hns]; exact pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
  rw [le_div_iff₀ hσ]
  exact hle

/-- **Summability of the Wold series.** The terms `b_j e_{t−j}` form a summable family in
`Lp ℝ 2 (pathLaw X P)`: they are pairwise orthogonal with square-summable norms
(`summable_sq_woldCoeff`), so summability follows from
`OrthogonalFamily.summable_iff_norm_sq_summable`. -/
theorem summable_woldError_smul (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) hE) (t : ℤ) :
    Summable (fun j => woldCoeff hE j • woldError pathCoord (pathLaw X P) hE (t - j)) := by
  have hv := orthonormal_woldError_smul hSS hmeas hE hσ t
  set sq := Real.sqrt (projErrorVariance pathCoord (pathLaw X P) hE) with hsqdef
  have hsq_pos : 0 < sq := Real.sqrt_pos.mpr hσ
  have hof := hv.orthogonalFamily
  set V := fun j : ℕ => LinearIsometry.toSpanSingleton ℝ (Lp ℝ 2 (pathLaw X P)) (hv.1 j) with hVdef
  have hVeq : ∀ j, V j (woldCoeff hE j * sq)
      = woldCoeff hE j • woldError pathCoord (pathLaw X P) hE (t - j) := by
    intro j
    simp only [hVdef, LinearIsometry.toSpanSingleton_apply, smul_smul, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hsq_pos), mul_one]
  have hkey : Summable (fun j => V j (woldCoeff hE j * sq)) := by
    rw [hof.summable_iff_norm_sq_summable (fun j => woldCoeff hE j * sq)]
    have hfun : (fun j => ‖woldCoeff hE j * sq‖ ^ 2)
        = (fun j => (woldCoeff hE j) ^ 2 * sq ^ 2) := by
      funext j; rw [Real.norm_eq_abs, sq_abs, mul_pow]
    rw [hfun]
    exact (summable_sq_woldCoeff hSS hmeas hE hσ).mul_right (sq ^ 2)
  simpa only [hVeq] using hkey

/-- **The deterministic (perfectly predictable) component** `µ_t = P_{−∞}[Y_t]`: the orthogonal
projection of `Y_t` onto the remote past. It is the part of `Y_t` recoverable from arbitrarily
distant history, and is the limit of the linear predictors `P_{t−m}[Y_t]` as `m → ∞`. -/
noncomputable def woldDeterministic (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) (t : ℤ) :
    Lp ℝ 2 (pathLaw X P) :=
  (remotePast pathCoord (pathLaw X P) hE).starProjection ((hE t).toLp)

/-- **The Wold series converges to the stochastic part.** `∑_j b_j e_{t−j}` sums (in `Lp`) to
`Y_t − µ_t`. The partial sums are the projection residuals `Y_t − P_{t−m}[Y_t]`
(`starProjection_pastSpan_sub_eq`), which converge to `Y_t − µ_t` by the remote-past limit
`tendsto_starProjection_pastSpan_sub`; summability pins the unordered sum to that limit. -/
theorem hasSum_woldSeries (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) hE) (t : ℤ) :
    HasSum (fun j => woldCoeff hE j • woldError pathCoord (pathLaw X P) hE (t - j))
      ((hE t).toLp - woldDeterministic hE t) := by
  have hHS := (summable_woldError_smul hSS hmeas hE hσ t).hasSum
  have hpartial : ∀ m : ℕ,
      ∑ j ∈ Finset.range m, woldCoeff hE j • woldError pathCoord (pathLaw X P) hE (t - j)
        = (hE t).toLp
          - (pastSpan pathCoord (pathLaw X P) hE (t - m)).starProjection ((hE t).toLp) := by
    intro m; rw [starProjection_pastSpan_sub_eq hSS hmeas hE t m]; abel
  have htend2 : Tendsto
      (fun m => ∑ j ∈ Finset.range m, woldCoeff hE j • woldError pathCoord (pathLaw X P) hE (t - j))
      atTop (𝓝 ((hE t).toLp - woldDeterministic hE t)) := by
    simp only [hpartial]
    exact tendsto_const_nhds.sub
      (tendsto_starProjection_pastSpan_sub (X := pathCoord) (P := pathLaw X P) (hX := hE) t
        ((hE t).toLp))
  have huniq := tendsto_nhds_unique hHS.tendsto_sum_nat htend2
  rwa [huniq] at hHS

/-- **The Wold series representation of `Y_t`.** `Y_t = µ_t + ∑_j b_j e_{t−j}`: the sum of the
deterministic component and the convergent innovation series. Immediate from `hasSum_woldSeries`. -/
theorem wold_series_repr (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) hE) (t : ℤ) :
    (hE t).toLp
      = woldDeterministic hE t
        + ∑' j, woldCoeff hE j • woldError pathCoord (pathLaw X P) hE (t - j) := by
  rw [(hasSum_woldSeries hSS hmeas hE hσ t).tsum_eq]; abel

/-- **Hansen Theorem 14.17 (Wold decomposition).** Every strictly stationary process with a
non-degenerate innovation variance `σ² > 0` admits a decomposition
`Y_t = µ_t + ∑_{j=0}^∞ b_j e_{t−j}` where:

* `b_j = ⟪e_{t−j}, Y_t⟫ / σ²` are the (time-invariant) Wold coefficients with `b_0 = 1` and
  `∑_j b_j² < ∞`;
* `e_t` is the one-step linear-prediction error (white noise, Theorem 14.16);
* `µ_t` is the deterministic component `P_{−∞}[Y_t]`, the limit of the linear predictors
  `P_{t−m}[Y_t]` as the horizon recedes.

The innovation series converges in `Lp ℝ 2 (pathLaw X P)`. This packages the named components
`woldCoeff`, `woldDeterministic`, `woldCoeff_zero`, `summable_sq_woldCoeff`, `wold_series_repr`, and
`tendsto_starProjection_pastSpan_sub`. -/
theorem wold_decomposition (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) hE) :
    ∃ (b : ℕ → ℝ) (μ : ℤ → Lp ℝ 2 (pathLaw X P)),
      b 0 = 1 ∧ Summable (fun j => (b j) ^ 2) ∧
      (∀ t, (hE t).toLp = μ t + ∑' j, b j • woldError pathCoord (pathLaw X P) hE (t - j)) ∧
      (∀ t, Tendsto
        (fun m : ℕ => (pastSpan pathCoord (pathLaw X P) hE (t - m)).starProjection ((hE t).toLp))
        atTop (𝓝 (μ t))) := by
  refine ⟨woldCoeff hE, woldDeterministic hE, woldCoeff_zero hE hσ,
    summable_sq_woldCoeff hSS hmeas hE hσ, wold_series_repr hSS hmeas hE hσ, fun t => ?_⟩
  exact tendsto_starProjection_pastSpan_sub (X := pathCoord) (P := pathLaw X P) (hX := hE) t
    ((hE t).toLp)

/-- **A purely non-deterministic (regular) process** — Hansen's condition for Theorem 14.18. The
deterministic component collapses to a constant: the remote-past projection of every `Y_t` is the
same multiple `µ • 1` of the intercept (necessarily `µ = E[Y_t]`). Equivalently, the remote past
carries no information beyond the mean. -/
def IsNonDeterministic (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P)) : Prop :=
  ∃ μ : ℝ, ∀ t : ℤ,
    (remotePast pathCoord (pathLaw X P) hE).starProjection ((hE t).toLp) = μ • oneLp (pathLaw X P)

/-- **Hansen Theorem 14.18 (Wold decomposition, non-deterministic case).** For a purely
non-deterministic strictly stationary process, the deterministic component is the constant mean, so
the decomposition simplifies to `Y_t = µ · 1 + ∑_{j=0}^∞ b_j e_{t−j}` with the same coefficients as
Theorem 14.17 (`b_0 = 1`, `∑_j b_j² < ∞`). A thin specialisation of `wold_series_repr`. -/
theorem wold_decomposition_of_nonDeterministic (hSS : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hE : ∀ s, MemLp (pathCoord s) 2 (pathLaw X P))
    (hσ : 0 < projErrorVariance pathCoord (pathLaw X P) hE) (hdet : IsNonDeterministic hE) :
    ∃ (b : ℕ → ℝ) (μ : ℝ), b 0 = 1 ∧ Summable (fun j => (b j) ^ 2) ∧
      ∀ t, (hE t).toLp
        = μ • oneLp (pathLaw X P)
          + ∑' j, b j • woldError pathCoord (pathLaw X P) hE (t - j) := by
  obtain ⟨μ, hμ⟩ := hdet
  refine ⟨woldCoeff hE, μ, woldCoeff_zero hE hσ, summable_sq_woldCoeff hSS hmeas hE hσ, fun t => ?_⟩
  rw [wold_series_repr hSS hmeas hE hσ t]
  unfold woldDeterministic
  rw [hμ t]

/-! ### Theorem 14.19 — the AR(∞) representation (Wiener–Masani): documented deferral

Hansen's Theorem 14.19 upgrades the Wold moving-average representation of a purely non-deterministic
process to a one-sided autoregressive representation `∑_{j=0}^∞ a_j Y_{t−j} = e_t` (an AR(∞) with
`a_0 = 1`). Hansen gives no proof, citing Wiener–Masani (1958) and Politis–McElroy (2020, Cor.
6.1.17). The result requires inverting the Wold transfer function `b(z) = ∑_j b_j z^j` in a weighted
`ℓ²` sense, which needs a spectral lower bound `|b(z)| ≥ δ` on the closed unit disk — a
Wiener-lemma-grade analytic input. Mathlib (v4.29) has no bridge between the formal power-series
inverse (`PowerSeries.inv`) and its analytic/summable evaluation, so this direction is **deferred**;
any in-project statement would have to assume essentially the conclusion. See
`inventory/ch14-inventory.md` for the standing deferral record. -/

end ProbabilityTheory
