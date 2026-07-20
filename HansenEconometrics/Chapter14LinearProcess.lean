import HansenEconometrics.Chapter14TimeSeries
import HansenEconometrics.ErgodicTheory.PathShift
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Chapter 14: Time Series — convergent linear processes and the AR(1) process

This file formalizes Hansen's *Econometrics* Chapter 14 §14.6 (the convergent linear process,
**Definition 14.3** and **Theorem 14.3**) and §14.22 (the AR(1) process, **Theorem 14.21**). It
builds on the strict-stationarity API of `HansenEconometrics.Chapter14TimeSeries`, in particular
the keystone `ProbabilityTheory.IsStrictlyStationary.comp_shiftEquivariant` (Hansen Theorem 14.2).

The time index is `ℤ` throughout (discrete time), which is an `AddCommGroup` and `Countable`, so the
shift `t ↦ t + j` and the keystone theorem both apply. The linear process is defined via `tsum`
(`∑'`), which is *total*: it returns the limit when the series converges and `0` otherwise. This
totality is what lets the shift-equivariance keystone apply without first establishing pointwise
convergence.

## Main declarations

* `ProbabilityTheory.linearProcess_summable_ae` — **Hansen Definition 14.3 / Theorem 14.3
  (convergence half).** For a strictly stationary, integrable scalar process `Y` and absolutely
  summable coefficients `a`, the linear-process series `∑' j, a j * Y (t - j)` converges a.s. The
  proof shows the nonnegative function `ω ↦ ∑' j, ‖a j * Y (t - j) ω‖ₑ` has finite Lebesgue
  integral (`= (∑' j, ‖a j‖ₑ) * ∫⁻ ‖Y 0‖ₑ`, using strict stationarity to make every `∫⁻ ‖Y s‖ₑ`
  equal to `∫⁻ ‖Y 0‖ₑ`), hence is a.e. finite, hence the series is a.e. absolutely summable.
* `ProbabilityTheory.IsStrictlyStationary.linearProcess` — **Hansen Theorem 14.3 (stationarity
  half).** The linear process `X t ω = ∑' j, a j * Y (t - j) ω` is strictly stationary. This is the
  shift-equivariant functional `φ p = ∑' j, a j * p (-(j : ℤ))` applied to the whole path of `Y`,
  so it follows from `comp_shiftEquivariant`.
* `ProbabilityTheory.IsErgodicProcess.linearProcess` — **Hansen Theorem 14.6 (ergodic half).** The
  same linear process `X t ω = ∑' j, a j * Y (t - j) ω` of an *ergodic* input `Y` is again ergodic,
  via the ergodic keystone `IsErgodicProcess.comp_shiftEquivariant` (Hansen Theorem 14.5). Theorem
  14.6 is Theorem 14.3 with ergodicity added; paired with the stationarity conclusion
  (`IsStrictlyStationary.linearProcess`, Theorem 14.3) this gives Theorem 14.6 in full — an
  absolutely convergent linear filter of a strictly stationary ergodic input is strictly stationary
  and ergodic.
* `ProbabilityTheory.ar1Process_strictlyStationary` — **Hansen Theorem 14.21 (strict-stationarity
  half).** The MA(∞) solution `Y t ω = μ + ∑' j, α₁ ^ j * e (t - j) ω` of the AR(1) recursion, with
  i.i.d. integrable innovations `e` and `|α₁| < 1`, is strictly stationary.
* `ProbabilityTheory.ar1Process_ergodic` — **Hansen Theorem 14.21 (ergodic half).** The same MA(∞)
  solution is ergodic: the i.i.d. innovations are ergodic (`IsErgodicProcess.of_iid`, Hansen Theorem
  14.4) and the geometric filter is shift-equivariant (`IsErgodicProcess.comp_shiftEquivariant`,
  Hansen Theorem 14.5). This completes the stochastic content of Hansen Theorem 14.21.
* `ProbabilityTheory.ar1Process_summable_ae` — **Hansen Theorem 14.21 (convergence).** The MA(∞)
  series defining the AR(1) solution converges a.s. (specialization of `linearProcess_summable_ae`
  with geometric coefficients `α₁ ^ j`).

The ergodic halves consume `HansenEconometrics.ErgodicTheory.PathShift` (the path-space shift bridge
and Hansen Theorems 14.4/14.5); the ergodic-theorem *consumption* (Hansen Theorem 14.9, the mean
ergodic LLN) lives downstream in `HansenEconometrics.ErgodicTheory.MeanErgodic`.
-/

open MeasureTheory Filter

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Measurability of a `tsum` of measurable real functions.** For a countable family `F i` of
measurable real-valued functions, the (total) pointwise sum `x ↦ ∑' i, F i x` is measurable.

Mathlib provides this only for `ℝ≥0∞`- and `ℝ≥0`-valued sums (`Measurable.ennreal_tsum`,
`Measurable.nnreal_tsum`); the signed real version is supplied here. The `tsum` is total (it returns
`0` where the family is not summable), so the proof splits on the convergence set
`conv = {x | ∃ c, Tendsto (Finset partial sums) atTop (𝓝 c)}`. That set is measurable
(`StronglyMeasurable.measurableSet_exists_tendsto`, using that `Finset ι` is countable so the net
filter is countably generated), and on it the `tsum` equals the limit `limUnder` of the partial-sum
net (measurable via `StronglyMeasurable.limUnder`); off it the `tsum` is `0`. -/
theorem measurable_tsum_real {ι α : Type*} [Countable ι] [MeasurableSpace α]
    {F : ι → α → ℝ} (hF : ∀ i, Measurable (F i)) :
    Measurable (fun x => ∑' i, F i x) := by
  classical
  -- Partial sums over the `Finset ι` net are measurable.
  set S : Finset ι → α → ℝ := fun s x => ∑ i ∈ s, F i x with hS
  have hS_meas : ∀ s : Finset ι, StronglyMeasurable (S s) := fun s =>
    (Finset.measurable_sum s fun i _ => hF i).stronglyMeasurable
  -- The convergence set of the partial-sum net is measurable.
  have hconv : MeasurableSet {x | ∃ c, Tendsto (fun s => S s x) atTop (𝓝 c)} :=
    MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto hS_meas
  -- The limit of the net is measurable.
  have hlim_meas : Measurable (fun x => limUnder atTop (fun s => S s x)) :=
    (MeasureTheory.StronglyMeasurable.limUnder hS_meas).measurable
  -- The total `tsum` agrees with the limit on the convergence set, and with `0` off it.
  have hpoint : (fun x => ∑' i, F i x)
      = fun x => if (∃ c, Tendsto (fun s => S s x) atTop (𝓝 c))
                 then limUnder atTop (fun s => S s x) else 0 := by
    funext x
    by_cases hx : ∃ c, Tendsto (fun s => S s x) atTop (𝓝 c)
    · rw [if_pos hx]
      obtain ⟨c, hc⟩ := hx
      have hsum : HasSum (fun i => F i x) c := hc
      rw [hsum.tsum_eq, hc.limUnder_eq]
    · rw [if_neg hx]
      refine tsum_eq_zero_of_not_summable ?_
      rintro ⟨c, hc⟩
      exact hx ⟨c, hc⟩
  rw [hpoint]
  exact hlim_meas.ite hconv measurable_const

omit [IsProbabilityMeasure P] in
/-- **Singleton identical distribution from strict stationarity.** For a strictly stationary scalar
process, every marginal `Y s` is identically distributed to `Y 0`. This mirrors the `hpt` helper
inside `IsStrictlyStationary.isCovarianceStationary`, specialized to anchor `0` and shift `s`. -/
theorem identDistrib_of_strictlyStationary {Y : ℤ → Ω → ℝ}
    (hY : IsStrictlyStationary Y P) (s : ℤ) :
    IdentDistrib (Y s) (Y 0) P P := by
  have hmem : (0 : ℤ) ∈ ({0} : Finset ℤ) := Finset.mem_singleton.mpr rfl
  have hSS₁ := hY {0} s
  have hcomp := hSS₁.comp (u := fun f : ({0} : Finset ℤ) → ℝ => f ⟨0, hmem⟩)
    (measurable_pi_apply _)
  have hcomp' : IdentDistrib (fun ω => Y (0 + s) ω) (fun ω => Y 0 ω) P P := hcomp
  simpa only [zero_add] using hcomp'

omit [IsProbabilityMeasure P] in
/-- **Strict stationarity makes the `enorm`-`lintegral` of each marginal constant.** Using
`identDistrib_of_strictlyStationary` and `IdentDistrib.lintegral_eq` (composed with the measurable
`enorm`), `∫⁻ ‖Y s‖ₑ = ∫⁻ ‖Y 0‖ₑ` for every `s`. -/
private theorem lintegral_enorm_eq_of_strictlyStationary {Y : ℤ → Ω → ℝ}
    (hY : IsStrictlyStationary Y P) (s : ℤ) :
    ∫⁻ ω, ‖Y s ω‖ₑ ∂P = ∫⁻ ω, ‖Y 0 ω‖ₑ ∂P :=
  ((identDistrib_of_strictlyStationary hY s).comp measurable_enorm).lintegral_eq

omit [IsProbabilityMeasure P] in
/-- **Hansen Definition 14.3 / Theorem 14.3 (convergence half).** For a strictly stationary,
integrable scalar process `Y` and absolutely summable real coefficients `a`, the linear-process
series `∑' j, a j * Y (t - j) ω` converges absolutely — hence converges — for almost every `ω`,
at every time `t`.

Proof outline (the clean Mathlib route, avoiding Hansen's Markov/Cauchy argument). The nonnegative
measurable function `ω ↦ ∑' j, ‖a j * Y (t - j) ω‖ₑ` has Lebesgue integral
`∑' j, ‖a j‖ₑ * ∫⁻ ‖Y (t - j)‖ₑ` by `lintegral_tsum` and `lintegral_const_mul''`. Strict
stationarity collapses each `∫⁻ ‖Y (t - j)‖ₑ` to the common value `M := ∫⁻ ‖Y 0‖ₑ`, so the integral
equals `(∑' j, ‖a j‖ₑ) * M`, which is finite (`M < ∞` because `Y 0` is integrable, and
`∑' j, ‖a j‖ₑ < ∞` because `a` is absolutely summable). A finite Lebesgue integral forces the
integrand to be a.e. finite (`ae_lt_top'`), and a finite `ℝ≥0∞`-tsum of norms is exactly a.e.
absolute summability (`ENNReal.tsum_coe_ne_top_iff_summable_coe`), whence a.e. summability
(`Summable.of_norm`). -/
theorem linearProcess_summable_ae {Y : ℤ → Ω → ℝ} {a : ℕ → ℝ}
    (hY : IsStrictlyStationary Y P) (hY_meas : ∀ t, AEMeasurable (Y t) P)
    (hY_int : Integrable (Y 0) P) (ha : Summable (fun j => |a j|)) (t : ℤ) :
    ∀ᵐ ω ∂P, Summable (fun j : ℕ => a j * Y (t - j) ω) := by
  -- Each summand `ω ↦ ‖a j * Y (t - j) ω‖ₑ` is `AEMeasurable`.
  have hsummand_meas : ∀ j : ℕ, AEMeasurable (fun ω => ‖a j * Y (t - j) ω‖ₑ) P := fun j =>
    (aemeasurable_const.mul (hY_meas (t - j))).enorm
  -- `M := ∫⁻ ‖Y 0‖ₑ` is finite because `Y 0` is integrable.
  have hM : ∫⁻ ω, ‖Y 0 ω‖ₑ ∂P ≠ ∞ := by
    have := hY_int.2
    rw [hasFiniteIntegral_iff_enorm] at this
    exact this.ne
  -- The coefficient `enorm`-tsum `∑' j, ‖a j‖ₑ` is finite, from absolute summability of `a`.
  have hcoeff : (∑' j : ℕ, ‖a j‖ₑ) ≠ ∞ := by
    have hsum_nn : Summable (fun j : ℕ => ‖a j‖₊) := by
      rw [← NNReal.summable_coe]
      simpa [coe_nnnorm, Real.norm_eq_abs] using ha
    simp only [enorm_eq_nnnorm]
    exact (ENNReal.tsum_coe_ne_top_iff_summable).mpr hsum_nn
  -- Compute the total `lintegral` of the tsum-of-enorms.
  have hkey : ∫⁻ ω, ∑' j : ℕ, ‖a j * Y (t - j) ω‖ₑ ∂P
      = (∑' j : ℕ, ‖a j‖ₑ) * ∫⁻ ω, ‖Y 0 ω‖ₑ ∂P := by
    rw [lintegral_tsum hsummand_meas]
    have hterm : ∀ j : ℕ, ∫⁻ ω, ‖a j * Y (t - j) ω‖ₑ ∂P
        = ‖a j‖ₑ * ∫⁻ ω, ‖Y 0 ω‖ₑ ∂P := by
      intro j
      simp only [enorm_mul]
      rw [lintegral_const_mul'' _ (hY_meas (t - j)).enorm,
        lintegral_enorm_eq_of_strictlyStationary hY (t - j)]
    rw [tsum_congr hterm, ENNReal.tsum_mul_right]
  -- The total is finite.
  have hfin : ∫⁻ ω, ∑' j : ℕ, ‖a j * Y (t - j) ω‖ₑ ∂P ≠ ∞ := by
    rw [hkey]
    exact ENNReal.mul_ne_top hcoeff hM
  -- Finite integral ⇒ integrand a.e. finite ⇒ a.e. summability.
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hsummand_meas) hfin
  filter_upwards [hae] with ω hω
  refine Summable.of_norm ?_
  have hsummable_nn : Summable (fun j : ℕ => (‖a j * Y (t - j) ω‖₊ : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    simpa only [enorm_eq_nnnorm] using hω.ne
  simpa [coe_nnnorm] using hsummable_nn

/-- **Hansen Theorem 14.3 (stationarity half).** The linear process
`X t ω = ∑' j, a j * Y (t - j) ω` of a strictly stationary process `Y` with real coefficients `a` is
again strictly stationary.

The process `X` is the measurable shift-equivariant functional `φ p = ∑' j, a j * p (-(j : ℤ))`
applied to the whole path `fun k => Y (t + k) ω` of `Y`, because
`φ (fun k => Y (t + k) ω) = ∑' j, a j * Y (t + (-(j : ℤ))) ω = ∑' j, a j * Y (t - j) ω`. Strict
stationarity then follows from `IsStrictlyStationary.comp_shiftEquivariant` (Hansen Theorem 14.2),
the keystone for stationarity of functionals of the history. Measurability of `φ` is the signed-real
`tsum` measurability `measurable_tsum_real`. Unlike the convergence half, this needs no summability
hypothesis on `a`: `tsum` is total, so the keystone applies regardless of pointwise convergence. -/
theorem IsStrictlyStationary.linearProcess {Y : ℤ → Ω → ℝ} {a : ℕ → ℝ}
    (hY : IsStrictlyStationary Y P) (hY_meas : ∀ t, AEMeasurable (Y t) P) :
    IsStrictlyStationary (fun t ω => ∑' j : ℕ, a j * Y (t - j) ω) P := by
  -- The shift-equivariant functional of the whole path.
  set φ : (ℤ → ℝ) → ℝ := fun p => ∑' j : ℕ, a j * p (-(j : ℤ)) with hφdef
  -- `φ` is measurable as a signed-real `tsum` of measurable coordinate functionals.
  have hφ : Measurable φ :=
    measurable_tsum_real fun j => measurable_const.mul (measurable_pi_apply _)
  -- Apply the keystone, then rewrite the resulting process to the linear-process form.
  have hkey : IsStrictlyStationary (fun t ω => φ (fun j => Y (t + j) ω)) P :=
    IsStrictlyStationary.comp_shiftEquivariant hφ hY hY_meas
  have heq : (fun t ω => φ (fun j => Y (t + j) ω))
      = fun t ω => ∑' j : ℕ, a j * Y (t - j) ω := by
    funext t ω
    simp only [hφdef]
    exact tsum_congr fun j => by rw [sub_eq_add_neg]
  rwa [heq] at hkey

omit [IsProbabilityMeasure P] in
/-- **Hansen Theorem 14.6 (ergodic half).** The linear process
`X t ω = ∑' j, a j * Y (t - j) ω` of an *ergodic* process `Y` with real coefficients `a` is again
ergodic. Hansen Theorem 14.6 strengthens Theorem 14.3 by adding ergodicity to both hypothesis and
conclusion; its stationarity conclusion is `IsStrictlyStationary.linearProcess` (Theorem 14.3), and
this theorem supplies the added ergodicity, so the two together give all of Theorem 14.6 (an
absolutely convergent linear filter of a strictly stationary, ergodic input is itself strictly
stationary and ergodic).

The proof mirrors the stationarity half exactly: `X` is the measurable shift-equivariant functional
`φ p = ∑' j, a j * p (-(j : ℤ))` applied to the whole path of `Y`, so ergodicity follows from
`IsErgodicProcess.comp_shiftEquivariant` (Hansen Theorem 14.5, the ergodic companion of Theorem
14.2). The resulting process expression is verbatim the one in `IsStrictlyStationary.linearProcess`,
so the two halves compose. As for the stationarity half, no summability hypothesis on `a` is needed:
`tsum` is total, so the keystone applies regardless of pointwise convergence. Ergodicity alone
drives the conclusion — `comp_shiftEquivariant` needs neither strict stationarity nor a
probability-measure hypothesis — so the only assumptions are ergodicity of `Y` and coordinatewise
`AEMeasurable`ility. -/
theorem IsErgodicProcess.linearProcess {Y : ℤ → Ω → ℝ} {a : ℕ → ℝ}
    (hYe : IsErgodicProcess Y P) (hY_meas : ∀ t, AEMeasurable (Y t) P) :
    IsErgodicProcess (fun t ω => ∑' j : ℕ, a j * Y (t - j) ω) P := by
  -- The shift-equivariant functional of the whole path (same `φ` as the stationarity half).
  set φ : (ℤ → ℝ) → ℝ := fun p => ∑' j : ℕ, a j * p (-(j : ℤ)) with hφdef
  -- `φ` is measurable as a signed-real `tsum` of measurable coordinate functionals.
  have hφ : Measurable φ :=
    measurable_tsum_real fun j => measurable_const.mul (measurable_pi_apply _)
  -- Apply the ergodic keystone, then rewrite the resulting process to the linear-process form.
  have hkey : IsErgodicProcess (fun t ω => φ (fun j => Y (t + j) ω)) P :=
    hYe.comp_shiftEquivariant hφ hY_meas
  have heq : (fun t ω => φ (fun j => Y (t + j) ω))
      = fun t ω => ∑' j : ℕ, a j * Y (t - j) ω := by
    funext t ω
    simp only [hφdef]
    exact tsum_congr fun j => by rw [sub_eq_add_neg]
  rwa [heq] at hkey

/-! ## The AR(1) process (Hansen §14.22, Theorem 14.21)

We model the stationary solution of the AR(1) recursion `Yₜ = α₀ + α₁ Yₜ₋₁ + eₜ` with `|α₁| < 1`
through its MA(∞) representation `Yₜ = μ + ∑ⱼ α₁ʲ eₜ₋ⱼ`, where `μ = α₀ / (1 - α₁)` and the
innovations `e` are i.i.d. and integrable. We establish the a.s. convergence of the MA(∞) series,
the strict stationarity of the solution (`ar1Process_strictlyStationary`), and — completing the
stochastic content of Hansen Theorem 14.21 — its ergodicity (`ar1Process_ergodic`), routing the
i.i.d. innovations through the path-space shift bridge of
`HansenEconometrics.ErgodicTheory.PathShift`. -/

/-- The geometric coefficients `α₁ ^ j` of the AR(1) MA(∞) representation are absolutely summable
when `|α₁| < 1`. -/
theorem summable_abs_geometric {α₁ : ℝ} (hα : |α₁| < 1) :
    Summable (fun j : ℕ => |α₁ ^ j|) := by
  have : (fun j : ℕ => |α₁ ^ j|) = fun j : ℕ => |α₁| ^ j := by
    funext j; rw [abs_pow]
  rw [this]
  exact summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg (abs_nonneg α₁)])

/-- **Hansen Theorem 14.21 (innovations are strictly stationary).** The i.i.d. innovation sequence
of an AR(1) process is strictly stationary (Hansen Theorem 14.1 applied to `e`). -/
theorem ar1Innovations_strictlyStationary {e : ℤ → Ω → ℝ}
    (he_indep : iIndepFun e P) (he_ident : ∀ t s, IdentDistrib (e t) (e s) P P)
    (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsStrictlyStationary e P :=
  IsStrictlyStationary.of_iid he_indep he_ident he_meas

/-- **Hansen Theorem 14.21 (a.s. convergence of the MA(∞) series).** For i.i.d. integrable
innovations `e` and `|α₁| < 1`, the geometric MA(∞) series `∑' j, α₁ ^ j * e (t - j) ω` converges
a.s. This specializes the linear-process convergence `linearProcess_summable_ae` to the geometric
coefficients `a j = α₁ ^ j` (absolutely summable by `summable_abs_geometric`), with `e` strictly
stationary (from `ar1Innovations_strictlyStationary`). -/
theorem ar1Process_summable_ae {e : ℤ → Ω → ℝ} {α₁ : ℝ}
    (he_indep : iIndepFun e P) (he_ident : ∀ t s, IdentDistrib (e t) (e s) P P)
    (he_meas : ∀ t, AEMeasurable (e t) P) (he_int : Integrable (e 0) P) (hα : |α₁| < 1) (t : ℤ) :
    ∀ᵐ ω ∂P, Summable (fun j : ℕ => α₁ ^ j * e (t - j) ω) :=
  linearProcess_summable_ae (ar1Innovations_strictlyStationary he_indep he_ident he_meas)
    he_meas he_int (summable_abs_geometric hα) t

/-- **Hansen Theorem 14.21 (strict stationarity of the AR(1) solution).** The MA(∞) solution
`Y t ω = μ + ∑' j, α₁ ^ j * e (t - j) ω` of the AR(1) recursion (with intercept `α₀`, coefficient
`α₁` satisfying `|α₁| < 1`, mean `μ = α₀ / (1 - α₁)`, and i.i.d. innovations `e`) is strictly
stationary.

As in `IsStrictlyStationary.linearProcess`, the solution is the measurable shift-equivariant
functional `φ p = μ + ∑' j, α₁ ^ j * p (-(j : ℤ))` of the whole innovation path; the added constant
`μ` keeps `φ` measurable. Strict stationarity of the i.i.d. innovations
(`ar1Innovations_strictlyStationary`) feeds the keystone
`IsStrictlyStationary.comp_shiftEquivariant` (Hansen Theorem 14.2).

The *ergodicity* half of Hansen Theorem 14.21 is `ar1Process_ergodic` (same functional `φ`, ergodic
keystone in place of the stationarity keystone). -/
theorem ar1Process_strictlyStationary {e : ℤ → Ω → ℝ} (α₀ α₁ : ℝ)
    (he_indep : iIndepFun e P) (he_ident : ∀ t s, IdentDistrib (e t) (e s) P P)
    (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsStrictlyStationary
      (fun t ω => α₀ / (1 - α₁) + ∑' j : ℕ, α₁ ^ j * e (t - j) ω) P := by
  set μ : ℝ := α₀ / (1 - α₁) with hμdef
  -- The shift-equivariant functional, with the intercept `μ` added to the geometric MA(∞) sum.
  set φ : (ℤ → ℝ) → ℝ := fun p => μ + ∑' j : ℕ, α₁ ^ j * p (-(j : ℤ)) with hφdef
  have hφ : Measurable φ :=
    measurable_const.add
      (measurable_tsum_real fun j => measurable_const.mul (measurable_pi_apply _))
  have hkey : IsStrictlyStationary (fun t ω => φ (fun j => e (t + j) ω)) P :=
    IsStrictlyStationary.comp_shiftEquivariant hφ
      (ar1Innovations_strictlyStationary he_indep he_ident he_meas) he_meas
  have heq : (fun t ω => φ (fun j => e (t + j) ω))
      = fun t ω => μ + ∑' j : ℕ, α₁ ^ j * e (t - j) ω := by
    funext t ω
    simp only [hφdef]
    exact congrArg (μ + ·) (tsum_congr fun j => by rw [sub_eq_add_neg])
  rwa [heq] at hkey

/-- **Hansen Theorem 14.21 (ergodicity of the AR(1) solution).** The MA(∞) solution
`Y t ω = μ + ∑' j, α₁ ^ j * e (t - j) ω` of the AR(1) recursion (with `μ = α₀ / (1 - α₁)` and i.i.d.
innovations `e`) is ergodic. Together with `ar1Process_strictlyStationary`, this completes the
stochastic content of Hansen Theorem 14.21: the AR(1) solution is strictly stationary *and* ergodic.

The i.i.d. innovations are ergodic by `IsErgodicProcess.of_iid` (Hansen Theorem 14.4), and the
solution is the measurable shift-equivariant functional `φ p = μ + ∑' j, α₁ ^ j * p (-(j : ℤ))` of
the innovation path, so `IsErgodicProcess.comp_shiftEquivariant` (Hansen Theorem 14.5) transports
ergodicity to `Y`. This parallels `ar1Process_strictlyStationary` step for step, reusing the same
functional `φ` and the same MA(∞) process expression, so the two halves compose. As there,
`|α₁| < 1` and integrability of `e` are not needed for the mere ergodicity conclusion (`tsum` is
total). -/
theorem ar1Process_ergodic {e : ℤ → Ω → ℝ} (α₀ α₁ : ℝ)
    (he_indep : iIndepFun e P) (he_ident : ∀ t s, IdentDistrib (e t) (e s) P P)
    (he_meas : ∀ t, AEMeasurable (e t) P) :
    IsErgodicProcess
      (fun t ω => α₀ / (1 - α₁) + ∑' j : ℕ, α₁ ^ j * e (t - j) ω) P := by
  set μ : ℝ := α₀ / (1 - α₁) with hμdef
  -- The shift-equivariant functional (the same `φ` as `ar1Process_strictlyStationary`).
  set φ : (ℤ → ℝ) → ℝ := fun p => μ + ∑' j : ℕ, α₁ ^ j * p (-(j : ℤ)) with hφdef
  have hφ : Measurable φ :=
    measurable_const.add
      (measurable_tsum_real fun j => measurable_const.mul (measurable_pi_apply _))
  -- The i.i.d. innovations are ergodic (Hansen Theorem 14.4).
  have he_ergodic : IsErgodicProcess e P :=
    IsErgodicProcess.of_iid he_indep he_ident he_meas
  -- Transport ergodicity along the functional, then rewrite to the MA(∞) form.
  have hkey : IsErgodicProcess (fun t ω => φ (fun j => e (t + j) ω)) P :=
    he_ergodic.comp_shiftEquivariant hφ he_meas
  have heq : (fun t ω => φ (fun j => e (t + j) ω))
      = fun t ω => μ + ∑' j : ℕ, α₁ ^ j * e (t - j) ω := by
    funext t ω
    simp only [hφdef]
    exact congrArg (μ + ·) (tsum_congr fun j => by rw [sub_eq_add_neg])
  rwa [heq] at hkey

/-- **Hansen Theorem 14.21 (the AR(1) recursion holds a.s.).** The MA(∞) solution
`Y t ω = μ + ∑' j, α₁ ^ j * e (t - j) ω` (with `μ = α₀ / (1 - α₁)` and `|α₁| < 1`) satisfies the
AR(1) recursion `Y t = α₀ + α₁ * Y (t - 1) + e t` for almost every `ω`.

The proof equates the MA(∞) series at `t` and `t - 1`. Splitting the first (`j = 0`) term off
`∑' j, α₁ ^ j e (t - j)` (via `Summable.tsum_eq_zero_add`) gives `e t + ∑' j, α₁ ^ (j+1) e (t-1-j)`,
while `α₁ * ∑' j, α₁ ^ j e (t-1-j) = ∑' j, α₁ ^ (j+1) e (t-1-j)` (pulling the constant into the sum
with `Summable.tsum_mul_left`). The intercepts match because `μ = α₀ / (1 - α₁)` gives
`α₀ + α₁ * μ = μ` (using `1 - α₁ ≠ 0`). Both the `t` and `t-1` MA(∞) series are summable a.s.
(`ar1Process_summable_ae`); the recursion holds on the intersection of those full-measure sets. -/
theorem ar1Process_recursion {e : ℤ → Ω → ℝ} (α₀ α₁ : ℝ)
    (he_indep : iIndepFun e P) (he_ident : ∀ t s, IdentDistrib (e t) (e s) P P)
    (he_meas : ∀ t, AEMeasurable (e t) P) (he_int : Integrable (e 0) P) (hα : |α₁| < 1) (t : ℤ) :
    ∀ᵐ ω ∂P, (fun t ω => α₀ / (1 - α₁) + ∑' j : ℕ, α₁ ^ j * e (t - j) ω) t ω
      = α₀ + α₁ * (fun t ω => α₀ / (1 - α₁) + ∑' j : ℕ, α₁ ^ j * e (t - j) ω) (t - 1) ω
        + e t ω := by
  have h1mα : (1 : ℝ) - α₁ ≠ 0 := by
    have : α₁ < 1 := (abs_lt.mp hα).2
    linarith
  -- `α₀ + α₁ * μ = μ`, the fixed-point identity for the AR(1) mean.
  have hμ : α₀ + α₁ * (α₀ / (1 - α₁)) = α₀ / (1 - α₁) := by
    field_simp
    ring
  -- The MA(∞) series is summable a.s. at both `t` and `t - 1`.
  have hSt := ar1Process_summable_ae he_indep he_ident he_meas he_int hα t
  have hSt1 := ar1Process_summable_ae he_indep he_ident he_meas he_int hα (t - 1)
  filter_upwards [hSt, hSt1] with ω hsum_t hsum_t1
  -- Split the `j = 0` term off the series at time `t`.
  rw [hsum_t.tsum_eq_zero_add]
  -- Pull `α₁` inside the series at time `t - 1`.
  have hmul : α₁ * ∑' j : ℕ, α₁ ^ j * e (t - 1 - j) ω
      = ∑' j : ℕ, α₁ ^ (j + 1) * e (t - 1 - j) ω := by
    rw [← hsum_t1.tsum_mul_left]
    exact tsum_congr fun j => by rw [pow_succ]; ring
  -- Reindex the tail of the series at time `t` to match the `t - 1` series.
  have htail : (∑' j : ℕ, α₁ ^ (j + 1) * e (t - (↑(j + 1))) ω)
      = ∑' j : ℕ, α₁ ^ (j + 1) * e (t - 1 - j) ω := by
    refine tsum_congr fun j => ?_
    have : t - (↑(j + 1) : ℤ) = t - 1 - (j : ℤ) := by push_cast; ring
    rw [this]
  rw [htail, ← hmul]
  -- Combine with the intercept identity and rearrange.
  rw [Nat.cast_zero, sub_zero, pow_zero, one_mul]
  linear_combination (-1 : ℝ) * hμ

end ProbabilityTheory
