import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Chapter 14: Time Series — strict and covariance stationarity

This file formalizes Hansen §14.4 Definition 14.2 (strict stationarity) and Hansen §14.14
(covariance stationarity) for a discrete- or continuous-time stochastic process.

## Main declarations

* `ProbabilityTheory.IsStrictlyStationary X P` — `X : ι → Ω → E` is strictly stationary
  under `P` if for every finite index set `I : Finset ι` and every shift `h : ι`, the joint
  law of `fun ω t => X (↑t + h) ω` equals that of `fun ω t => X (↑t) ω` under `P`. This is
  expressed via `ProbabilityTheory.IdentDistrib` on `Finset`-restricted families, matching
  the API of `Mathlib.Probability.Process.FiniteDimensionalLaws`.
* `ProbabilityTheory.IsStrictlyStationary.of_iid` — **Hansen Theorem 14.1**: an i.i.d.
  family of random variables is strictly stationary. Independence is `iIndepFun` and
  identical distribution is `IdentDistrib (Y t) (Y s) P P` for all `t, s`.
* `ProbabilityTheory.IsCovarianceStationary X P` — **Hansen §14.14**: a real-valued process
  `X : ι → Ω → ℝ` is covariance stationary (a.k.a. weak / second-order / wide-sense
  stationary) if each `X t` is square-integrable, the mean `∫ X t ∂P` is constant in `t`,
  and the covariance `cov[X (t+h), X (s+h); P]` is shift-invariant.
* `ProbabilityTheory.autocovAt`, `ProbabilityTheory.autocov` — the autocovariance of a
  process evaluated at a time `t` and lag `h`, and its canonical lag-only form.
* `ProbabilityTheory.IsStrictlyStationary.isCovarianceStationary` — **bridge theorem**:
  a strictly stationary, square-integrable process is covariance stationary.
* `ProbabilityTheory.IsStrictlyStationary.identDistrib_path` — **bridge lemma**: upgrades the
  finite-restriction `IsStrictlyStationary` form to a full-path `IdentDistrib` between the
  shifted and unshifted whole paths, via `identDistrib_iff_forall_finset_identDistrib`.
* `ProbabilityTheory.IsStrictlyStationary.comp_shiftEquivariant` — **Hansen Theorem 14.2**: a
  measurable functional `φ` of the whole shifted path `fun j => Y (t + j)` of a strictly
  stationary process is again strictly stationary. Hansen's causal function of the history
  `(Yₜ, Yₜ₋₁, …)` is the special case where `φ` ignores the positive coordinates.
* `ProbabilityTheory.autocov_zero` — **Hansen §14.14**: `γ(0) = Var[X₀]`.
* `ProbabilityTheory.IsCovarianceStationary.autocovAt_eq_autocov` — **Hansen §14.14**: the
  autocovariance of a covariance-stationary process depends only on the lag, not the time.
* `ProbabilityTheory.IsCovarianceStationary.autocov_neg` — **Hansen §14.14**: the
  autocovariance function is symmetric in the lag, `γ(-h) = γ(h)`.

The index type `ι` only needs `[Add ι]` so the definitions cover `ℕ`, `ℤ`, `ℝ`, `ℝ≥0`.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- **Hansen Definition 14.2.** A family of random variables `X : ι → Ω → E` is
*strictly stationary* under `P` if, for every finite index set `I : Finset ι` and every
shift `h : ι`, the joint distribution of the shifted restriction
`fun ω => I.restrict (fun t => X (t + h) ω)` equals that of the unshifted restriction
`fun ω => I.restrict (fun t => X t ω)` under `P`.

The equality of joint laws is expressed via `ProbabilityTheory.IdentDistrib`, in the
finite-dimensional-distribution style of
`Mathlib.Probability.Process.FiniteDimensionalLaws`. Strict stationarity is preserved by
arbitrary measurable functionals of the past (Hansen Theorem 14.2). -/
def IsStrictlyStationary [Add ι] (X : ι → Ω → E) (P : Measure Ω) : Prop :=
  ∀ (I : Finset ι) (h : ι),
    IdentDistrib (fun ω => I.restrict (fun t => X (t + h) ω))
                 (fun ω => I.restrict (fun t => X t ω)) P P

/-- **Hansen Theorem 14.1.** An i.i.d. family of random variables is strictly stationary.

Here "i.i.d." is unpacked into mathlib pieces:
* `hY_indep : iIndepFun Y P` — the family is independent;
* `hY_ident : ∀ t s, IdentDistrib (Y t) (Y s) P P` — all marginals share one law;
* `hY_meas : ∀ t, AEMeasurable (Y t) P` — each `Y t` is `AEMeasurable`.

We additionally require `[IsProbabilityMeasure P]` because the mathlib
`iIndepFun ↔ infinitePi`-product characterisation lives there, `[Countable ι]` so the
infinite-product description of the joint law applies, and `[AddRightCancelSemigroup ι]`
so that the index shift `t ↦ t + h` is injective (true for `ℕ`, `ℤ`, `ℝ`). -/
theorem IsStrictlyStationary.of_iid [AddRightCancelSemigroup ι] [Countable ι]
    {Y : ι → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ t s, IdentDistrib (Y t) (Y s) P P)
    (hY_meas : ∀ t, AEMeasurable (Y t) P) :
    IsStrictlyStationary Y P := by
  -- The shifted family `fun t => Y (t + h)` is also iid, with the same common law as `Y`.
  -- Then the joint laws agree as `infinitePi`-products, so all finite restrictions agree.
  intro I h
  set Yshift : ι → Ω → E := fun t ω => Y (t + h) ω with hYshift
  -- Shifted family is `AEMeasurable`.
  have hYshift_meas : ∀ t, AEMeasurable (Yshift t) P := fun t => hY_meas (t + h)
  -- Shifted family is independent: reindex by the injective map `t ↦ t + h`.
  have hYshift_indep : iIndepFun Yshift P := by
    have hinj : Function.Injective (fun t : ι => t + h) := fun a b hab => by
      simpa using add_right_cancel hab
    simpa [hYshift, Function.comp] using hY_indep.precomp hinj
  -- It suffices to prove the full-process laws agree, then restrict.
  rw [show (fun ω => I.restrict (fun t => Y (t + h) ω)) =
        (fun ω => I.restrict (fun t => Yshift t ω)) from rfl]
  refine ((identDistrib_iff_forall_finset_identDistrib ?_ ?_).mp ?_) I
  · exact aemeasurable_pi_iff.mpr hYshift_meas
  · exact aemeasurable_pi_iff.mpr hY_meas
  -- The joint laws of `Yshift` and `Y` agree because both are the infinite product of the
  -- common one-dimensional law of `Y t` (independent of `t` by `hY_ident`).
  refine ⟨aemeasurable_pi_iff.mpr hYshift_meas, aemeasurable_pi_iff.mpr hY_meas, ?_⟩
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀' hYshift_meas).mp hYshift_indep,
    (iIndepFun_iff_map_fun_eq_infinitePi_map₀' hY_meas).mp hY_indep]
  have hlaw : (fun t => P.map (Yshift t)) = fun t => P.map (Y t) := by
    funext t
    exact (hY_ident (t + h) t).map_eq
  rw [hlaw]

/-- **Hansen §14.14 — covariance stationarity.** A real-valued process
`X : ι → Ω → ℝ` is *covariance stationary* under `P` if:
(1) each `X t` is square-integrable (`MemLp (X t) 2 P`);
(2) the mean is shift-invariant, `∫ X (t + h) ∂P = ∫ X t ∂P` for all `t, h`;
(3) the covariance is shift-invariant,
`cov[X (t + h), X (s + h); P] = cov[X t, X s; P]` for all `t s h : ι`.

This is also called weak, second-order, or wide-sense stationarity. Conditions (2) and (3)
together imply Hansen's "constant mean / covariance depends only on the lag" formulation
once `ι` has the appropriate cancellation structure (e.g. `ℤ`, `ℝ`): from shift invariance
of the mean one obtains `∫ X s ∂P = ∫ X t ∂P` whenever some `h` satisfies `t + h = s`. The
shift-invariant form is stated here so the definition needs only `[Add ι]`, covering `ℕ`,
`ℤ`, `ℝ`, `ℝ≥0`. -/
structure IsCovarianceStationary [Add ι] (X : ι → Ω → ℝ) (P : Measure Ω) : Prop where
  /-- Each marginal `X t` is square-integrable. -/
  memLp : ∀ t, MemLp (X t) 2 P
  /-- The mean `∫ X t ∂P` is shift-invariant. -/
  integral_shift : ∀ t h, ∫ ω, X (t + h) ω ∂P = ∫ ω, X t ω ∂P
  /-- The covariance `cov[X (t+h), X (s+h); P]` is independent of the shift `h`. -/
  covariance_shift : ∀ t s h,
    covariance (X (t + h)) (X (s + h)) P = covariance (X t) (X s) P

/-- **Autocovariance at time `t` and lag `h`** of a real-valued process
`X : ι → Ω → ℝ` under `P`. Defined as `cov[X t, X (t + h); P]`. For a
covariance-stationary process this depends only on the lag `h` (see `autocov`). -/
noncomputable def autocovAt [Add ι] (X : ι → Ω → ℝ) (P : Measure Ω) (t h : ι) : ℝ :=
  covariance (X t) (X (t + h)) P

/-- **Lag-`h` autocovariance** of a real-valued process `X : ι → Ω → ℝ` under `P`,
anchored at the index `0`. Defined as `autocovAt X P 0 h = cov[X 0, X h; P]`.
For covariance-stationary processes this equals `autocovAt X P t h` for every `t`. -/
noncomputable def autocov [Add ι] [Zero ι] (X : ι → Ω → ℝ) (P : Measure Ω) (h : ι) : ℝ :=
  autocovAt X P 0 h

/-- **Bridge: strict stationarity implies covariance stationarity.** A strictly stationary,
square-integrable real-valued process is covariance stationary.

Proof outline. Strict stationarity at the singleton `{t}` (resp. pair `{t, s}`) composed
with the coordinate evaluation map yields
`IdentDistrib (X (t + h)) (X t) P P` (resp. the analogous fact for pairs of evaluations),
which transfers integrals via `IdentDistrib.integral_eq`. The covariance is rewritten as
`P[X (t+h) * X (s+h)] - P[X (t+h)] * P[X (s+h)]` via `covariance_eq_sub`, and the mean and
mean-of-product transfer separately. -/
theorem IsStrictlyStationary.isCovarianceStationary [Add ι] {X : ι → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hSS : IsStrictlyStationary X P) (hMemLp : ∀ t, MemLp (X t) 2 P) :
    IsCovarianceStationary X P := by
  -- Singleton identical-distribution: pair `X (t+h)` and `X t`.
  have hpt : ∀ t h : ι, IdentDistrib (X (t + h)) (X t) P P := by
    intro t h
    have hmem : t ∈ ({t} : Finset ι) := Finset.mem_singleton.mpr rfl
    have hSS₁ := hSS {t} h
    have hcomp := hSS₁.comp (u := fun f : ({t} : Finset ι) → ℝ => f ⟨t, hmem⟩)
      (measurable_pi_apply _)
    simpa [Function.comp, Finset.restrict] using hcomp
  -- Pair identical-distribution: pair `(X (t+h), X (s+h))` with `(X t, X s)`.
  have hpair : ∀ t s h : ι,
      IdentDistrib (fun ω => (X (t + h) ω, X (s + h) ω))
                   (fun ω => (X t ω, X s ω)) P P := by
    intro t s h
    classical
    by_cases hts : t = s
    · -- diagonal: reduce to the singleton case via the diagonal map
      subst hts
      have h₁ : IdentDistrib (X (t + h)) (X t) P P := hpt t h
      have h₂ := h₁.comp (u := fun x : ℝ => (x, x))
        (by exact (measurable_id.prodMk measurable_id))
      simpa [Function.comp] using h₂
    · -- off-diagonal: use the pair Finset `{t, s}` (DecidableEq via classical)
      have hmemt : t ∈ ({t, s} : Finset ι) := by
        simp
      have hmems : s ∈ ({t, s} : Finset ι) := by
        simp
      have hSS₂ := hSS ({t, s} : Finset ι) h
      have hcomp := hSS₂.comp
        (u := fun f : (({t, s} : Finset ι) : Finset ι) → ℝ =>
          (f ⟨t, hmemt⟩, f ⟨s, hmems⟩))
        (by exact (measurable_pi_apply _).prodMk (measurable_pi_apply _))
      simpa [Function.comp, Finset.restrict] using hcomp
  refine ⟨hMemLp, ?_, ?_⟩
  · -- mean shift-invariance: direct from `hpt` via `IdentDistrib.integral_eq`.
    intro t h
    exact (hpt t h).integral_eq
  · intro t s h
    -- Covariance shift invariance: rewrite both sides via `covariance_eq_sub`
    -- and transfer each summand using `hpair` and `hpt`.
    have h₁ : MemLp (X (t + h)) 2 P := hMemLp _
    have h₂ : MemLp (X (s + h)) 2 P := hMemLp _
    have h₃ : MemLp (X t) 2 P := hMemLp _
    have h₄ : MemLp (X s) 2 P := hMemLp _
    rw [covariance_eq_sub h₁ h₂, covariance_eq_sub h₃ h₄]
    have hmean_t : ∫ ω, X (t + h) ω ∂P = ∫ ω, X t ω ∂P := (hpt t h).integral_eq
    have hmean_s : ∫ ω, X (s + h) ω ∂P = ∫ ω, X s ω ∂P := (hpt s h).integral_eq
    have hprod := (hpair t s h).comp (u := fun p : ℝ × ℝ => p.1 * p.2)
      (measurable_fst.mul measurable_snd)
    have hprod_int : ∫ ω, X (t + h) ω * X (s + h) ω ∂P
        = ∫ ω, X t ω * X s ω ∂P := by
      simpa [Function.comp] using hprod.integral_eq
    -- Goal: ∫ X(t+h)·X(s+h) - ∫X(t+h) · ∫X(s+h) = ∫ X t · X s - ∫X t · ∫X s.
    -- The notation `P[X t * X s]` is `∫ ω, (X t * X s) ω ∂P = ∫ ω, X t ω * X s ω ∂P`.
    have hprod_int' :
        ∫ ω, (X (t + h) * X (s + h)) ω ∂P = ∫ ω, (X t * X s) ω ∂P := by
      simpa [Pi.mul_apply] using hprod_int
    rw [hprod_int', hmean_t, hmean_s]

/-- **Full-path shift-invariance from strict stationarity.** For a strictly stationary,
`AEMeasurable` family `X : ι → Ω → E` over a finite measure, the whole shifted path
`fun ω t => X (t + h) ω` is identically distributed to the whole path `fun ω t => X t ω`.

This upgrades the finite-restriction `IsStrictlyStationary` form to a single full-path
`IdentDistrib` statement, using `identDistrib_iff_forall_finset_identDistrib` (the same
equivalence used in `IsStrictlyStationary.of_iid`). It is the reusable engine behind
Hansen Theorem 14.2 (`IsStrictlyStationary.comp_shiftEquivariant`). -/
theorem IsStrictlyStationary.identDistrib_path [Add ι] [Countable ι] {X : ι → Ω → E}
    {P : Measure Ω} [IsFiniteMeasure P] (hX : IsStrictlyStationary X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (h : ι) :
    IdentDistrib (fun ω => fun t => X (t + h) ω) (fun ω => fun t => X t ω) P P :=
  (identDistrib_iff_forall_finset_identDistrib
      (aemeasurable_pi_iff.mpr fun t => hmeas (t + h))
      (aemeasurable_pi_iff.mpr hmeas)).mpr (fun I => hX I h)

/-- **Hansen Theorem 14.2.** If `Y` is strictly stationary and `X t = φ((Y (t + j))ⱼ)` is a
measurable functional of the whole shifted path, then `X` is strictly stationary.

This is the shift-equivariant functional form of Hansen's theorem: a fixed measurable
functional `φ : (ι → E) → F` is applied to each shifted whole path
`fun j => Y (t + j) ω`. Hansen's causal "function of the history `(Yₜ, Yₜ₋₁, …)`" is the
special case where `φ` ignores the strictly positive coordinates. Stating it for
functionals of the whole path needs only `[Countable ι]` (discrete time, the relevant case
for time series) together with the weakest additive structure — `[AddCommMonoid ι]` — that
lets the index regrouping `(t + j) + h = (t + h) + j` go through. -/
theorem IsStrictlyStationary.comp_shiftEquivariant
    [AddCommMonoid ι] [Countable ι] {F : Type*} [MeasurableSpace F]
    {Y : ι → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]
    {φ : (ι → E) → F} (hφ : Measurable φ)
    (hY : IsStrictlyStationary Y P) (hY_meas : ∀ t, AEMeasurable (Y t) P) :
    IsStrictlyStationary (fun t ω => φ (fun j => Y (t + j) ω)) P := by
  -- The path map `Φ` reproduces each `X t` coordinatewise; it is measurable and
  -- intertwines the index shift `t ↦ t + h`.
  set Φ : (ι → E) → (ι → F) := fun p => fun t => φ (fun j => p (t + j)) with hΦdef
  have hΦ : Measurable Φ := by
    refine measurable_pi_iff.mpr fun t => hφ.comp ?_
    exact measurable_pi_iff.mpr fun j => measurable_pi_apply (t + j)
  -- `Φ` sends the unshifted `Y`-path to the `X`-path.
  have hbase : ∀ ω, Φ (fun t => Y t ω) = fun t => φ (fun j => Y (t + j) ω) := fun ω => rfl
  -- `Φ` sends the `h`-shifted `Y`-path to the `h`-shifted `X`-path (regrouping indices).
  have hshift : ∀ ω h, Φ (fun t => Y (t + h) ω)
      = fun t => φ (fun j => Y ((t + h) + j) ω) := by
    intro ω h
    funext t
    simp only [hΦdef]
    exact congrArg φ (funext fun j => congrArg (fun i => Y i ω) (add_right_comm t j h))
  -- Transport the full-path `IdentDistrib` of `Y` through `Φ`, then restrict back.
  intro I h
  have hid := ((hY.identDistrib_path hY_meas h).comp hΦ)
  have hX_meas : ∀ t, AEMeasurable (fun ω => φ (fun j => Y (t + j) ω)) P := fun t =>
    hφ.comp_aemeasurable (aemeasurable_pi_iff.mpr fun j => hY_meas (t + j))
  refine ((identDistrib_iff_forall_finset_identDistrib
      (aemeasurable_pi_iff.mpr fun t => hX_meas (t + h))
      (aemeasurable_pi_iff.mpr hX_meas)).mp ?_) I
  have hLHS : (Φ ∘ fun ω => fun t => Y (t + h) ω)
      = fun ω => fun t => φ (fun j => Y ((t + h) + j) ω) := funext fun ω => hshift ω h
  have hRHS : (Φ ∘ fun ω => fun t => Y t ω)
      = fun ω => fun t => φ (fun j => Y (t + j) ω) := funext fun ω => hbase ω
  rw [hLHS, hRHS] at hid
  exact hid

/-- **Hansen §14.14.** The lag-`0` autocovariance is the variance of the process:
`γ(0) = Var[X₀]`. Requires `[AddZeroClass ι]` so that `autocov` (anchored at `0`) is defined
and the index identity `0 + 0 = 0` holds, and `AEMeasurable (X 0) P` to invoke
`covariance_self`. -/
theorem autocov_zero [AddZeroClass ι] {X : ι → Ω → ℝ} {P : Measure Ω}
    (hX : AEMeasurable (X 0) P) : autocov X P 0 = variance (X 0) P := by
  rw [autocov, autocovAt, add_zero, covariance_self hX]

/-- **Hansen §14.14.** For a covariance-stationary process the autocovariance depends only
on the lag, not on the time index: `autocovAt X P t h = autocov X P h` for every `t`. -/
theorem IsCovarianceStationary.autocovAt_eq_autocov [AddCommMonoid ι] {X : ι → Ω → ℝ}
    {P : Measure Ω} (hX : IsCovarianceStationary X P) (t h : ι) :
    autocovAt X P t h = autocov X P h := by
  rw [autocov, autocovAt, autocovAt, zero_add]
  have := hX.covariance_shift 0 h t
  rwa [zero_add, add_comm h t] at this

/-- **Hansen §14.14.** The autocovariance function of a covariance-stationary process is
symmetric in the lag: `γ(-h) = γ(h)`. Requires `[AddCommGroup ι]` so that the lag `-h`
makes sense. -/
theorem IsCovarianceStationary.autocov_neg [AddCommGroup ι] {X : ι → Ω → ℝ} {P : Measure Ω}
    (hX : IsCovarianceStationary X P) (h : ι) :
    autocov X P (-h) = autocov X P h := by
  rw [autocov, autocov, autocovAt, autocovAt, zero_add, zero_add, covariance_comm]
  have := hX.covariance_shift (-h) 0 h
  rw [neg_add_cancel, zero_add] at this
  exact this.symm

end ProbabilityTheory
