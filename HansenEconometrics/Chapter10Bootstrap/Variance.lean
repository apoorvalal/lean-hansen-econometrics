import HansenEconometrics.Chapter10Bootstrap.DeltaMethod

/-!
# Chapter 10 — Bootstrap variance

Bootstrap variance consistency for resampled means and smooth functions:
moment-convergence, weak-distribution, uniform-square-tail, and Lindeberg-tail
routes, their indexed variants, and the delta-method Gaussian variance
capstones.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section SmoothFunctionBootstrapVariance

/-- Smooth-function plug-in covariance functional `Gᵀ V G`.

This is the covariance map in Hansen's smooth-function bootstrap delta-method
results, with `G` the Jacobian and `V` the covariance matrix of the underlying
moment/statistic. -/
noncomputable def smoothFunctionVarianceFunctional
    {d r : Type*} [Fintype d] [Fintype r]
    (G : Matrix d r ℝ) (V : Matrix d d ℝ) : Matrix r r ℝ :=
  Gᵀ * V * G

/-- The smooth-function plug-in covariance map is continuous in its Jacobian
and covariance inputs. -/
private theorem smoothFunctionVarianceFunctional_continuous
    {d r : Type*} [Fintype d] [Fintype r] :
    Continuous (fun p : Matrix d r ℝ × Matrix d d ℝ =>
      smoothFunctionVarianceFunctional p.1 p.2) := by
  unfold smoothFunctionVarianceFunctional
  exact ((continuous_fst.matrix_transpose).matrix_mul continuous_snd).matrix_mul
    continuous_fst

/-- Hansen Theorem 10.8, plug-in covariance continuous-mapping bridge.

If the bootstrap Jacobian/covariance pair converges in bootstrap probability to
the population pair, then the smooth-function covariance plug-in
`Gstarᵀ Vstar Gstar` converges in bootstrap probability to `Gᵀ V G`.  The
concrete Theorem 10.8 constructors provide the joint bootstrap-probability
premise from the smooth-function model and the bootstrap WLLN/CLT layer. -/
theorem chapter10_bootstrap_smooth_variance_consistency
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ℕ → Ω → Ωs → Matrix d r ℝ}
    {Vstar : ℕ → Ω → Ωs → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hGV :
      TendstoInBootstrapProbability μ Pstar
        (fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
        (fun _ => (G, V))) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  TendstoInBootstrapProbability.continuousAt_const_comp
    (E := Matrix d r ℝ × Matrix d d ℝ)
    (F := Matrix r r ℝ)
    (Pstar := Pstar)
    (Zstar := fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
    (c := (G, V))
    (g := fun p => smoothFunctionVarianceFunctional p.1 p.2)
    hPstar hGV smoothFunctionVarianceFunctional_continuous.continuousAt

/-- Hansen Theorem 10.8, componentwise plug-in covariance bridge.

This wrapper packages the usual proof shape: establish separate bootstrap
convergence of the plug-in Jacobian and covariance inputs, combine them into a
joint convergence statement, then apply the smooth covariance CMT. -/
theorem chapter10_bootstrap_smooth_variance_consistency_of_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ℕ → Ω → Ωs → Matrix d r ℝ}
    {Vstar : ℕ → Ω → Ωs → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG :
      TendstoInBootstrapProbability μ Pstar Gstar (fun _ => G))
    (hV :
      TendstoInBootstrapProbability μ Pstar Vstar (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_consistency hPstar
    (TendstoInBootstrapProbability.prodMk hPstar hG hV)

/-- Hansen Theorem 10.8, plug-in covariance bridge from ordinary component
convergence.

This wrapper covers the common plug-in case where the bootstrap component
statistics are deterministic under the resampling law.  Ordinary convergence in
probability of `G_n` and `V_n` is lifted to bootstrap-probability convergence by
Theorem 10.1, then fed through the smooth covariance continuous-mapping bridge. -/
theorem chapter10_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gseq : ℕ → Ω → Matrix d r ℝ}
    {Vseq : ℕ → Ω → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hV : TendstoInMeasure μ Vseq atTop (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ => smoothFunctionVarianceFunctional (Gseq n ω) (Vseq n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_consistency_of_components hPstar
    (chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
      (μ := μ) (Pstar := Pstar) hPstar hG)
    (chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
      (μ := μ) (Pstar := Pstar) hPstar hV)

/-- Hansen Theorem 10.8, plug-in covariance bridge from continuous stochastic
component maps.

This is the CMT-shaped constructor for stochastic plug-in Jacobian/covariance
inputs: if a bootstrap statistic `Ustar` converges to a constant `u` and the
Jacobian and covariance plug-ins are continuous at `u`, then
`G(Ustar)ᵀ V(Ustar) G(Ustar)` converges to `G(u)ᵀ V(u) G(u)`. -/
theorem chapter10_bootstrap_smooth_variance_consistency_of_continuous_plugins
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Ustar : ℕ → Ω → Ωs → A} {u : A}
    {Gfun : A → Matrix d r ℝ} {Vfun : A → Matrix d d ℝ}
    (hU : TendstoInBootstrapProbability μ Pstar Ustar (fun _ => u))
    (hG : ContinuousAt Gfun u) (hV : ContinuousAt Vfun u) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (Vfun (Ustar n ω ωs)))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (Vfun u)) :=
  chapter10_bootstrap_smooth_variance_consistency_of_components hPstar
    (TendstoInBootstrapProbability.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hG)
    (TendstoInBootstrapProbability.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hV)

/-- Hansen Theorem 10.8, mixed stochastic Jacobian plug-in bridge.

This covers the common case where the Jacobian is a continuous function of a
bootstrap plug-in statistic, while the covariance input has its own convergence
proof, such as a conditional covariance or finite-replication covariance
route. -/
theorem
    chapter10_bootstrap_smooth_variance_consistency_of_continuous_jacobian
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Ustar : ℕ → Ω → Ωs → A} {u : A}
    {Gfun : A → Matrix d r ℝ}
    {Vstar : ℕ → Ω → Ωs → Matrix d d ℝ} {V : Matrix d d ℝ}
    (hU : TendstoInBootstrapProbability μ Pstar Ustar (fun _ => u))
    (hG : ContinuousAt Gfun u)
    (hV : TendstoInBootstrapProbability μ Pstar Vstar (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) V) :=
  chapter10_bootstrap_smooth_variance_consistency_of_components hPstar
    (TendstoInBootstrapProbability.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hG)
    hV

/-- Hansen Theorem 10.8, deterministic continuous plug-in covariance bridge.

This wrapper covers the common smooth-function case where the plug-in source
statistic is non-random under the bootstrap law: ordinary convergence in
probability of `U_n` to `u`, plus continuity of the Jacobian and covariance
plug-in maps at `u`, implies bootstrap convergence of `G(U_n)' V(U_n) G(U_n)`. -/
theorem chapter10_bootstrap_smooth_variance_consistency_of_deterministic_plugins
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Useq : ℕ → Ω → A} {u : A}
    {Gfun : A → Matrix d r ℝ} {Vfun : A → Matrix d d ℝ}
    (hU : TendstoInMeasure μ Useq atTop (fun _ => u))
    (hG : ContinuousAt Gfun u) (hV : ContinuousAt Vfun u) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gfun (Useq n ω))
          (Vfun (Useq n ω)))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (Vfun u)) :=
  chapter10_bootstrap_smooth_variance_consistency_of_continuous_plugins
    (μ := μ) (Pstar := Pstar) (Ustar := fun n ω _ => Useq n ω) (u := u)
    (Gfun := Gfun) (Vfun := Vfun) hPstar
    (chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
      (μ := μ) (Pstar := Pstar) hPstar hU)
    hG hV

/-- Hansen Theorem 10.8, mixed deterministic Jacobian plug-in bridge.

Ordinary convergence in probability of a non-bootstrap plug-in statistic
supplies the continuous Jacobian input, while a separate ordinary convergence
proof supplies the covariance input; Theorem 10.1 lifts both to bootstrap
probability before the smooth covariance CMT is applied. -/
theorem
    chapter10_bootstrap_smooth_variance_consistency_of_deterministic_jacobian
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Useq : ℕ → Ω → A} {u : A}
    {Gfun : A → Matrix d r ℝ}
    {Vseq : ℕ → Ω → Matrix d d ℝ} {V : Matrix d d ℝ}
    (hU : TendstoInMeasure μ Useq atTop (fun _ => u))
    (hG : ContinuousAt Gfun u)
    (hV : TendstoInMeasure μ Vseq atTop (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gfun (Useq n ω)) (Vseq n ω))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) V) :=
  chapter10_bootstrap_smooth_variance_consistency_of_continuous_jacobian
    (μ := μ) (Pstar := Pstar)
    (Ustar := fun n ω _ => Useq n ω) (u := u) (Gfun := Gfun)
    (Vstar := fun n ω _ => Vseq n ω) (V := V) hPstar
    (chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
      (μ := μ) (Pstar := Pstar) hPstar hU)
    hG
    (chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
      (μ := μ) (Pstar := Pstar) hPstar hV)

/-- Indexed Hansen Theorem 10.8, plug-in covariance continuous-mapping bridge
for sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_smooth_variance_consistency
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ∀ n, Ω → Ωboot n → Matrix d r ℝ}
    {Vstar : ∀ n, Ω → Ωboot n → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hGV :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
        (fun _ => (G, V))) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  TendstoInBootstrapProbabilityIndexed.continuousAt_const_comp
    (E := Matrix d r ℝ × Matrix d d ℝ)
    (F := Matrix r r ℝ)
    (Pstar := Pstar)
    (Zstar := fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
    (c := (G, V))
    (g := fun p => smoothFunctionVarianceFunctional p.1 p.2)
    hPstar hGV smoothFunctionVarianceFunctional_continuous.continuousAt

/-- Indexed Hansen Theorem 10.8, componentwise plug-in covariance bridge. -/
theorem chapter10_indexed_bootstrap_smooth_variance_consistency_of_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ∀ n, Ω → Ωboot n → Matrix d r ℝ}
    {Vstar : ∀ n, Ω → Ωboot n → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG :
      TendstoInBootstrapProbabilityIndexed μ Pstar Gstar (fun _ => G))
    (hV :
      TendstoInBootstrapProbabilityIndexed μ Pstar Vstar (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency hPstar
    (TendstoInBootstrapProbabilityIndexed.prodMk hPstar hG hV)

/-- Indexed Hansen Theorem 10.8, plug-in covariance bridge from ordinary
component convergence. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gseq : ℕ → Ω → Matrix d r ℝ}
    {Vseq : ℕ → Ω → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hV : TendstoInMeasure μ Vseq atTop (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ => smoothFunctionVarianceFunctional (Gseq n ω) (Vseq n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_components hPstar
    (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := Pstar) hPstar hG)
    (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := Pstar) hPstar hV)

/-- Indexed Hansen Theorem 10.8, plug-in covariance bridge from continuous
stochastic component maps. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_continuous_plugins
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Ustar : ∀ n, Ω → Ωboot n → A} {u : A}
    {Gfun : A → Matrix d r ℝ} {Vfun : A → Matrix d d ℝ}
    (hU : TendstoInBootstrapProbabilityIndexed μ Pstar Ustar (fun _ => u))
    (hG : ContinuousAt Gfun u) (hV : ContinuousAt Vfun u) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (Vfun (Ustar n ω ωs)))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (Vfun u)) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_components hPstar
    (TendstoInBootstrapProbabilityIndexed.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hG)
    (TendstoInBootstrapProbabilityIndexed.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hV)

/-- Indexed Hansen Theorem 10.8, mixed stochastic Jacobian plug-in bridge. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_continuous_jacobian
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Ustar : ∀ n, Ω → Ωboot n → A} {u : A}
    {Gfun : A → Matrix d r ℝ}
    {Vstar : ∀ n, Ω → Ωboot n → Matrix d d ℝ} {V : Matrix d d ℝ}
    (hU : TendstoInBootstrapProbabilityIndexed μ Pstar Ustar (fun _ => u))
    (hG : ContinuousAt Gfun u)
    (hV : TendstoInBootstrapProbabilityIndexed μ Pstar Vstar (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) V) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_components hPstar
    (TendstoInBootstrapProbabilityIndexed.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hG)
    hV

/-- Indexed Hansen Theorem 10.8, deterministic continuous plug-in covariance
bridge. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_deterministic_plugins
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Useq : ℕ → Ω → A} {u : A}
    {Gfun : A → Matrix d r ℝ} {Vfun : A → Matrix d d ℝ}
    (hU : TendstoInMeasure μ Useq atTop (fun _ => u))
    (hG : ContinuousAt Gfun u) (hV : ContinuousAt Vfun u) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gfun (Useq n ω))
          (Vfun (Useq n ω)))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (Vfun u)) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_continuous_plugins
    (μ := μ) (Pstar := Pstar) (Ustar := fun n ω _ => Useq n ω) (u := u)
    (Gfun := Gfun) (Vfun := Vfun) hPstar
    (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := Pstar) hPstar hU)
    hG hV

/-- Indexed Hansen Theorem 10.8, mixed deterministic Jacobian plug-in bridge. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_deterministic_jacobian
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Useq : ℕ → Ω → A} {u : A}
    {Gfun : A → Matrix d r ℝ}
    {Vseq : ℕ → Ω → Matrix d d ℝ} {V : Matrix d d ℝ}
    (hU : TendstoInMeasure μ Useq atTop (fun _ => u))
    (hG : ContinuousAt Gfun u)
    (hV : TendstoInMeasure μ Vseq atTop (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gfun (Useq n ω)) (Vseq n ω))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) V) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_continuous_jacobian
    (μ := μ) (Pstar := Pstar)
    (Ustar := fun n ω _ => Useq n ω) (u := u) (Gfun := Gfun)
    (Vstar := fun n ω _ => Vseq n ω) (V := V) hPstar
    (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := Pstar) hPstar hU)
    hG
    (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := Pstar) hPstar hV)

end SmoothFunctionBootstrapVariance

section BootstrapVariance

/-- Conditional bootstrap mean of a real statistic. -/
noncomputable def bootstrapMeanReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[Zstar n ω]

/-- Conditional bootstrap second moment of a real statistic. -/
noncomputable def bootstrapSecondMomentReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[(Zstar n ω) ^ 2]

/-- Conditional bootstrap variance of a real statistic. -/
noncomputable def bootstrapVarianceReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Var[Zstar n ω; Pstar n ω]

/-- Indexed conditional bootstrap mean of a real statistic. -/
noncomputable def bootstrapMeanRealIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[Zstar n ω]

/-- Indexed conditional bootstrap second moment of a real statistic. -/
noncomputable def bootstrapSecondMomentRealIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[(Zstar n ω) ^ 2]

/-- Indexed conditional bootstrap variance of a real statistic. -/
noncomputable def bootstrapVarianceRealIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Var[Zstar n ω; Pstar n ω]

/-- Indexed conditional mean of the normalized scalar ordinary
nonparametric-bootstrap mean.

For the `Fin (n+1) -> Fin (n+1)` resampling space, the CLT-scaled centered
bootstrap mean has exact conditional mean zero. -/
theorem bootstrapMeanRealIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_zero
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    bootstrapMeanRealIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
        n ω =
      0 := by
  simpa [bootstrapMeanRealIndexed, Fintype.card_fin, smul_eq_mul] using
    (integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Indexed conditional second moment of the normalized scalar ordinary
nonparametric-bootstrap mean.

The raw second moment of the CLT-scaled centered bootstrap mean is the finite
empirical one-draw variance. -/
theorem
    bootstrapSecondMomentRealIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_variance
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    bootstrapSecondMomentRealIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
        n ω =
      Var[fun i : Fin (n + 1) => Y i.val ω;
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))] := by
  simpa [bootstrapSecondMomentRealIndexed] using
    integral_sq_normalized_finSucc_resampleMean_sub_empiricalMean_eq_variance
      (Y := Y) n ω

/-- Indexed conditional variance of the normalized scalar ordinary
nonparametric-bootstrap mean.

The conditional variance API agrees exactly with the finite empirical one-draw
variance, matching the scalar CLT-scale covariance calculation. -/
theorem
    bootstrapVarianceRealIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_variance
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    bootstrapVarianceRealIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
        n ω =
      Var[fun i : Fin (n + 1) => Y i.val ω;
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))] := by
  simpa [bootstrapVarianceRealIndexed, Fintype.card_fin] using
    (variance_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Indexed conditional variance convergence for the normalized scalar
ordinary nonparametric-bootstrap mean from empirical one-draw variance
convergence.

This is the scalar Theorem 10.9 surface for the concrete
`Fin (n+1) -> Fin (n+1)` resampling law: the exact finite identity above
reduces the bootstrap conditional variance to the finite empirical variance. -/
theorem
    chapter10_indexed_bootstrap_variance_finSucc_resampleMean_tendsto_of_empirical_variance
    (Y : ℕ → Ω → ℝ) {v : ℝ}
    (hvar :
      TendstoInMeasure μ
        (fun n ω =>
          Var[fun i : Fin (n + 1) => Y i.val ω;
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))])
        atTop (fun _ => v)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))))
      atTop (fun _ => v) := by
  refine TendstoInMeasure.congr
    (f := fun n ω =>
      Var[fun i : Fin (n + 1) => Y i.val ω;
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))])
    (f' := bootstrapVarianceRealIndexed
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))))
    (g := fun _ : Ω => v) (g' := fun _ : Ω => v)
    (fun n => ?_) EventuallyEq.rfl hvar
  exact ae_of_all μ fun ω =>
    (bootstrapVarianceRealIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_variance
      (Y := Y) n ω).symm

/-- Pointwise bootstrap mean clipping error bound by an absolute-tail integral. -/
theorem bootstrapMeanReal_abs_sub_realClip_le_two_mul_integral_tail_abs
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R) (n : ℕ) (ω : Ω) :
    |bootstrapMeanReal Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| ≤
      2 * ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := by
  haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapMeanReal] using
    abs_integral_sub_realClip_le_two_mul_integral_tail_abs
      (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR

/-- Bootstrap mean clipping errors vanish in probability when their
absolute-tail integrals vanish in probability. -/
theorem bootstrapMeanReal_sub_realClip_tendsto_zero_of_tail_integral
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R)
    (hTail :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        bootstrapMeanReal Pstar Zstar n ω -
          (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
      atTop (fun _ => 0) := by
  have hTail2 := TendstoInMeasure.const_mul_zero_real (μ := μ) 2 hTail
  refine TendstoInMeasure.of_abs_le_zero_real hTail2 ?_
  intro n ω
  have hbound :=
    bootstrapMeanReal_abs_sub_realClip_le_two_mul_integral_tail_abs
      hPstar hZ hR n ω
  have htail_nonneg :
      0 ≤ ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := by
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => abs_nonneg (Zstar n ω ωs)) ωs
  calc
    |bootstrapMeanReal Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| ≤
        2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := hbound
    _ = |2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω| := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) htail_nonneg)]

/-- Pointwise bootstrap second-moment clipping error bound by a squared-tail
integral. -/
theorem bootstrapSecondMomentReal_abs_sub_realClip_sq_le_two_mul_integral_tail_sq
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R) (n : ℕ) (ω : Ω) :
    |bootstrapSecondMomentReal Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| ≤
      2 * ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := by
  haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapSecondMomentReal] using
    abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
      (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR

/-- Bootstrap second-moment clipping errors vanish in probability when their
squared-tail integrals vanish in probability. -/
theorem bootstrapSecondMomentReal_sub_realClip_sq_tendsto_zero_of_tail_integral
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R)
    (hTail :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        bootstrapSecondMomentReal Pstar Zstar n ω -
          (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
      atTop (fun _ => 0) := by
  have hTail2 := TendstoInMeasure.const_mul_zero_real (μ := μ) 2 hTail
  refine TendstoInMeasure.of_abs_le_zero_real hTail2 ?_
  intro n ω
  have hbound :=
    bootstrapSecondMomentReal_abs_sub_realClip_sq_le_two_mul_integral_tail_sq
      hPstar hZ hR n ω
  have htail_nonneg :
      0 ≤ ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := by
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
  calc
    |bootstrapSecondMomentReal Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| ≤
        2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := hbound
    _ = |2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω| := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) htail_nonneg)]

/-- Tail-integral constructor for the first-moment clipping premise used in
Hansen Theorem 10.9. -/
theorem bootstrapMeanReal_realClip_tails_of_tail_integrals
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZlim : Integrable Z ν)
    (hZstar : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω))
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapMeanReal Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0) := by
  intro ε hε
  obtain ⟨R, hR, hlimTail, hsourceTail⟩ := hTail (ε / 2) (by positivity)
  refine ⟨R, hR, ?_, ?_⟩
  · have hclip :=
      abs_integral_sub_realClip_le_two_mul_integral_tail_abs
        (μ := ν) (Y := Z) hZlim hR
    calc
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤
          2 * ∫ ωlim,
            Set.indicator {ωlim | R ≤ |Z ωlim|}
              (fun ωlim => |Z ωlim|) ωlim ∂ν := hclip
      _ ≤ 2 * (ε / 2) := by nlinarith
      _ = ε := by ring
  · exact bootstrapMeanReal_sub_realClip_tendsto_zero_of_tail_integral
      (μ := μ) hPstar hZstar hR hsourceTail

/-- Tail-integral constructor for the second-moment clipping premise used in
Hansen Theorem 10.9. -/
theorem bootstrapSecondMomentReal_realClip_tails_of_tail_integrals
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hZstar : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentReal Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0) := by
  intro ε hε
  obtain ⟨R, hR, hlimTail, hsourceTail⟩ := hTail (ε / 2) (by positivity)
  refine ⟨R, hR, ?_, ?_⟩
  · have hclip :=
      abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
        (μ := ν) (Y := Z) hZlim hR
    calc
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤
          2 * ∫ ωlim,
            Set.indicator {ωlim | R ≤ |Z ωlim|}
              (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := hclip
      _ ≤ 2 * (ε / 2) := by nlinarith
      _ = ε := by ring
  · exact bootstrapSecondMomentReal_sub_realClip_sq_tendsto_zero_of_tail_integral
      (μ := μ) hPstar hZstar hR hsourceTail

/-- Indexed bootstrap mean clipping errors vanish in probability when their
absolute-tail integrals vanish in probability. -/
theorem bootstrapMeanRealIndexed_sub_realClip_tendsto_zero_of_tail_integral
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R)
    (hTail :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        bootstrapMeanRealIndexed Pstar Zstar n ω -
          (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
      atTop (fun _ => 0) := by
  have hTail2 := TendstoInMeasure.const_mul_zero_real (μ := μ) 2 hTail
  refine TendstoInMeasure.of_abs_le_zero_real hTail2 ?_
  intro n ω
  have hbound :
      |bootstrapMeanRealIndexed Pstar Zstar n ω -
        (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| ≤
        2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := by
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapMeanRealIndexed] using
      abs_integral_sub_realClip_le_two_mul_integral_tail_abs
        (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR
  have htail_nonneg :
      0 ≤ ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω :=
    integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => abs_nonneg (Zstar n ω ωs)) ωs
  calc
    |bootstrapMeanRealIndexed Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| ≤
        2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := hbound
    _ = |2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω| := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) htail_nonneg)]

/-- Indexed bootstrap second-moment clipping errors vanish in probability when
their squared-tail integrals vanish in probability. -/
theorem bootstrapSecondMomentRealIndexed_sub_realClip_sq_tendsto_zero_of_tail_integral
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R)
    (hTail :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
          (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
      atTop (fun _ => 0) := by
  have hTail2 := TendstoInMeasure.const_mul_zero_real (μ := μ) 2 hTail
  refine TendstoInMeasure.of_abs_le_zero_real hTail2 ?_
  intro n ω
  have hbound :
      |bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
        (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| ≤
        2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := by
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapSecondMomentRealIndexed] using
      abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
        (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR
  have htail_nonneg :
      0 ≤ ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω :=
    integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
  calc
    |bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| ≤
        2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := hbound
    _ = |2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω| := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) htail_nonneg)]

/-- Indexed tail-integral constructor for the first-moment clipping premise
used in Hansen Theorem 10.9. -/
theorem bootstrapMeanRealIndexed_realClip_tails_of_tail_integrals
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZlim : Integrable Z ν)
    (hZstar : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω))
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapMeanRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0) := by
  intro ε hε
  obtain ⟨R, hR, hlimTail, hsourceTail⟩ := hTail (ε / 2) (by positivity)
  refine ⟨R, hR, ?_, ?_⟩
  · have hclip :=
      abs_integral_sub_realClip_le_two_mul_integral_tail_abs
        (μ := ν) (Y := Z) hZlim hR
    calc
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤
          2 * ∫ ωlim,
            Set.indicator {ωlim | R ≤ |Z ωlim|}
              (fun ωlim => |Z ωlim|) ωlim ∂ν := hclip
      _ ≤ 2 * (ε / 2) := by nlinarith
      _ = ε := by ring
  · exact bootstrapMeanRealIndexed_sub_realClip_tendsto_zero_of_tail_integral
      (μ := μ) hPstar hZstar hR hsourceTail

/-- Indexed tail-integral constructor for the second-moment clipping premise
used in Hansen Theorem 10.9. -/
theorem bootstrapSecondMomentRealIndexed_realClip_tails_of_tail_integrals
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hZstar : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0) := by
  intro ε hε
  obtain ⟨R, hR, hlimTail, hsourceTail⟩ := hTail (ε / 2) (by positivity)
  refine ⟨R, hR, ?_, ?_⟩
  · have hclip :=
      abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
        (μ := ν) (Y := Z) hZlim hR
    calc
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤
          2 * ∫ ωlim,
            Set.indicator {ωlim | R ≤ |Z ωlim|}
              (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := hclip
      _ ≤ 2 * (ε / 2) := by nlinarith
      _ = ε := by ring
  · exact bootstrapSecondMomentRealIndexed_sub_realClip_sq_tendsto_zero_of_tail_integral
      (μ := μ) hPstar hZstar hR hsourceTail

/-- Conditional absolute-tail integrals vanish in probability when dominated
by squared-tail integrals at a threshold at least one. -/
theorem bootstrapTailAbsIntegral_tendsto_zero_of_tailSqIntegral
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {R : ℝ} (hR : 1 ≤ R)
    (hTailSq :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hTailSq
  · intro n ω
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => abs_nonneg (Zstar n ω ωs)) ωs
  · intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact integral_tail_abs_le_integral_tail_sq_of_one_le
      (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR

/-- Indexed conditional absolute-tail integrals vanish in probability when
dominated by squared-tail integrals at a threshold at least one. -/
theorem bootstrapTailAbsIntegralIndexed_tendsto_zero_of_tailSqIntegral
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {R : ℝ} (hR : 1 ≤ R)
    (hTailSq :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hTailSq
  · intro n ω
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => abs_nonneg (Zstar n ω ωs)) ωs
  · intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact integral_tail_abs_le_integral_tail_sq_of_one_le
      (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR

/-- Conditional variance equals second moment minus squared conditional mean. -/
theorem bootstrapVarianceReal_eq_secondMoment_sub_mean_sq
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (n : ℕ) (ω : Ω) :
    bootstrapVarianceReal Pstar Zstar n ω =
      bootstrapSecondMomentReal Pstar Zstar n ω -
        (bootstrapMeanReal Pstar Zstar n ω) ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapVarianceReal, bootstrapSecondMomentReal, bootstrapMeanReal]
    using (ProbabilityTheory.variance_eq_sub (μ := Pstar n ω) (X := Zstar n ω)
      (hZ n ω))

/-- Indexed conditional variance equals second moment minus squared conditional
mean. -/
theorem bootstrapVarianceRealIndexed_eq_secondMoment_sub_mean_sq
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (n : ℕ) (ω : Ω) :
    bootstrapVarianceRealIndexed Pstar Zstar n ω =
      bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
        (bootstrapMeanRealIndexed Pstar Zstar n ω) ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapVarianceRealIndexed, bootstrapSecondMomentRealIndexed,
    bootstrapMeanRealIndexed] using
      (ProbabilityTheory.variance_eq_sub (μ := Pstar n ω) (X := Zstar n ω)
        (hZ n ω))

/-- Hansen Theorem 10.9, variance-consistency moment bridge.

If the conditional bootstrap first and second moments of a real statistic
converge in ordinary probability to the corresponding limit moments, then the
conditional bootstrap variance converges in probability to the variance
functional `m₂ - m²`.  The remaining Theorem 10.9 constructors show how
bootstrap distribution plus uniform square integrability imply these moment
premises, and how finite bootstrap replications estimate this conditional
variance. -/
theorem chapter10_bootstrap_variance_consistency_of_moment_convergence
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => m₂ - m ^ 2) := by
  have hmean_sq :
      TendstoInMeasure μ
        (fun n ω => bootstrapMeanReal Pstar Zstar n ω *
          bootstrapMeanReal Pstar Zstar n ω)
        atTop (fun _ => m * m) :=
    TendstoInMeasure.mul_limits_real hmean hmean
  have hsecond0 := TendstoInMeasure.sub_limit_zero_real hsecond
  have hmean_sq0 := TendstoInMeasure.sub_limit_zero_real hmean_sq
  have hdiff0 :
      TendstoInMeasure μ
        (fun n ω =>
          (bootstrapSecondMomentReal Pstar Zstar n ω -
            bootstrapMeanReal Pstar Zstar n ω *
              bootstrapMeanReal Pstar Zstar n ω) -
            (m₂ - m * m))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hsecond0 hmean_sq0
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
    refine ae_of_all μ fun ω => ?_
    ring
  have hdiff :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentReal Pstar Zstar n ω -
            bootstrapMeanReal Pstar Zstar n ω *
              bootstrapMeanReal Pstar Zstar n ω)
        atTop (fun _ => m₂ - m * m) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hvar :
      TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
        (fun _ => m₂ - m * m) := by
    refine TendstoInMeasure.congr
      (f := fun n ω =>
        bootstrapSecondMomentReal Pstar Zstar n ω -
          bootstrapMeanReal Pstar Zstar n ω *
            bootstrapMeanReal Pstar Zstar n ω)
      (f' := bootstrapVarianceReal Pstar Zstar)
      (g := fun _ : Ω => m₂ - m * m)
      (g' := fun _ : Ω => m₂ - m * m)
      (fun n => ?_) EventuallyEq.rfl hdiff
    refine ae_of_all μ fun ω => ?_
    rw [bootstrapVarianceReal_eq_secondMoment_sub_mean_sq hPstar hZ]
    ring
  simpa [pow_two] using hvar

/-- Indexed Hansen Theorem 10.9, variance-consistency moment bridge. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => m₂ - m ^ 2) := by
  have hmean_sq :
      TendstoInMeasure μ
        (fun n ω => bootstrapMeanRealIndexed Pstar Zstar n ω *
          bootstrapMeanRealIndexed Pstar Zstar n ω)
        atTop (fun _ => m * m) :=
    TendstoInMeasure.mul_limits_real hmean hmean
  have hsecond0 := TendstoInMeasure.sub_limit_zero_real hsecond
  have hmean_sq0 := TendstoInMeasure.sub_limit_zero_real hmean_sq
  have hdiff0 :
      TendstoInMeasure μ
        (fun n ω =>
          (bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            bootstrapMeanRealIndexed Pstar Zstar n ω *
              bootstrapMeanRealIndexed Pstar Zstar n ω) -
            (m₂ - m * m))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hsecond0 hmean_sq0
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
    refine ae_of_all μ fun ω => ?_
    ring
  have hdiff :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            bootstrapMeanRealIndexed Pstar Zstar n ω *
              bootstrapMeanRealIndexed Pstar Zstar n ω)
        atTop (fun _ => m₂ - m * m) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hvar :
      TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
        (fun _ => m₂ - m * m) := by
    refine TendstoInMeasure.congr
      (f := fun n ω =>
        bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
          bootstrapMeanRealIndexed Pstar Zstar n ω *
            bootstrapMeanRealIndexed Pstar Zstar n ω)
      (f' := bootstrapVarianceRealIndexed Pstar Zstar)
      (g := fun _ : Ω => m₂ - m * m)
      (g' := fun _ : Ω => m₂ - m * m)
      (fun n => ?_) EventuallyEq.rfl hdiff
    refine ae_of_all μ fun ω => ?_
    rw [bootstrapVarianceRealIndexed_eq_secondMoment_sub_mean_sq hPstar hZ]
    ring
  simpa [pow_two] using hvar

/-- Hansen Theorem 10.10, smooth-function variance-consistency wrapper.

In the smooth-function model, Hansen's bounded-derivative argument is used to
prove uniform square integrability and hence the conditional first/second
moment convergence premises. Once those moment premises are available, the
untrimmed bootstrap variance consistency conclusion is exactly the Theorem
10.9 moment bridge. -/
theorem chapter10_smooth_bootstrap_variance_consistency_of_moment_convergence
    {Pstar : ℕ → Ω → Measure Ωs} {ZthetaStar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (ZthetaStar n ω) 2 (Pstar n ω))
    {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar ZthetaStar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar ZthetaStar) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar ZthetaStar) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZ hmean hsecond

/-- Indexed Hansen Theorem 10.10, smooth-function variance-consistency wrapper.

This is the sample-size-dependent bootstrap-space version of
`chapter10_smooth_bootstrap_variance_consistency_of_moment_convergence`. -/
theorem chapter10_indexed_smooth_bootstrap_variance_consistency_of_moment_convergence
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {ZthetaStar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (ZthetaStar n ω) 2 (Pstar n ω))
    {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar ZthetaStar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar ZthetaStar) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar ZthetaStar) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZ hmean hsecond

/-- Hansen Theorem 10.9, weak-distribution plus UI/tail variance bridge.

Bootstrap weak convergence gives clipped first and second moment convergence.
If the supplied clipping-tail controls remove the clipping, the conditional
bootstrap variance converges to the variance functional of the limit law. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_realClip_tails
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapMeanReal Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0))
    (hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentReal Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
        (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
    simpa [bootstrapMeanReal] using
      hweak.integral_tendsto_of_realClip_tails hTailMean
  have hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
    simpa [bootstrapSecondMomentReal] using
      hweak.integral_sq_tendsto_of_realClip_tails hTailSecond
  exact chapter10_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZmem hmean hsecond

/-- Indexed Hansen Theorem 10.9, weak-distribution plus UI/tail variance
bridge. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_realClip_tails
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapMeanRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0))
    (hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
    simpa [bootstrapMeanRealIndexed] using
      hweak.integral_tendsto_of_realClip_tails hTailMean
  have hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
    simpa [bootstrapSecondMomentRealIndexed] using
      hweak.integral_sq_tendsto_of_realClip_tails hTailSecond
  exact chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZmem hmean hsecond

/-- Indexed Hansen Theorem 10.9, weak-distribution plus concrete
tail-integral variance bridge.

This is the sample-size-dependent bootstrap-space version of
`chapter10_bootstrap_variance_consistency_of_weak_distribution_tail_integrals`. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_tail_integrals
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0))
    (hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstarInt : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    exact memLp_one_iff_integrable.mp ((hZmem n ω).mono_exponent one_le_two)
  have hZlimInt : Integrable Z ν :=
    memLp_one_iff_integrable.mp (hZlim.mono_exponent one_le_two)
  exact chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_realClip_tails
    (μ := μ) (ν := ν) hPstar hZmem hweak
    (bootstrapMeanRealIndexed_realClip_tails_of_tail_integrals
      (μ := μ) (ν := ν) hPstarFinite hZlimInt hZstarInt hTailMean)
    (bootstrapSecondMomentRealIndexed_realClip_tails_of_tail_integrals
      (μ := μ) (ν := ν) hPstarFinite hZlim hZmem hTailSecond)

/-- Indexed Hansen Theorem 10.9, weak-distribution plus
squared-tail-integral variance bridge.

For thresholds at least one, squared tails dominate absolute tails, so one
indexed squared-tail control supplies the first- and second-tail integral
premises needed for conditional bootstrap variance consistency. -/
theorem
    chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_square_tail_integrals
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq ε hε
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hlimAbsLe :=
        integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := ν) (Y := Z) hZlim hR_one
      exact hlimAbsLe.trans hlimSq
    · exact bootstrapTailAbsIntegralIndexed_tendsto_zero_of_tailSqIntegral
        (μ := μ) hPstarFinite hZmem hR_one hsourceSq
  have hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq ε hε
    exact ⟨R, zero_le_one.trans hR_one, hlimSq, hsourceSq⟩
  exact chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_tail_integrals
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailMean hTailSecond

/-- Hansen Theorem 10.9, weak-distribution plus concrete tail-integral
variance bridge.

This packages the clipping-tail premises of
`chapter10_bootstrap_variance_consistency_of_weak_distribution_realClip_tails`
from conditional first- and second-tail integral controls.  Uniform square
integrability supplies those tail-integral controls in the textbook proof. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_tail_integrals
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0))
    (hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstarInt : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    exact memLp_one_iff_integrable.mp ((hZmem n ω).mono_exponent one_le_two)
  have hZlimInt : Integrable Z ν :=
    memLp_one_iff_integrable.mp (hZlim.mono_exponent one_le_two)
  exact chapter10_bootstrap_variance_consistency_of_weak_distribution_realClip_tails
    (μ := μ) (ν := ν) hPstar hZmem hweak
    (bootstrapMeanReal_realClip_tails_of_tail_integrals
      (μ := μ) (ν := ν) hPstarFinite hZlimInt hZstarInt hTailMean)
    (bootstrapSecondMomentReal_realClip_tails_of_tail_integrals
      (μ := μ) (ν := ν) hPstarFinite hZlim hZmem hTailSecond)

/-- Hansen Theorem 10.9, weak-distribution plus squared-tail-integral
variance bridge.

For thresholds at least one, squared tails dominate absolute tails.  Thus a
single uniform-square-tail control supplies both the first- and second-tail
integral premises needed for conditional bootstrap variance consistency. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_square_tail_integrals
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq ε hε
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hlimAbsLe :=
        integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := ν) (Y := Z) hZlim hR_one
      exact hlimAbsLe.trans hlimSq
    · exact bootstrapTailAbsIntegral_tendsto_zero_of_tailSqIntegral
        (μ := μ) hPstarFinite hZmem hR_one hsourceSq
  have hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq ε hε
    exact ⟨R, zero_le_one.trans hR_one, hlimSq, hsourceSq⟩
  exact chapter10_bootstrap_variance_consistency_of_weak_distribution_tail_integrals
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailMean hTailSecond

/-- Textbook-style uniform square-tail condition for Hansen Theorem 10.9.

For every tolerance, a threshold can be chosen so that the limit squared tail is
small and the corresponding conditional bootstrap squared tail is small in
probability.  This is the conditional two-probability-space form of uniform
square integrability used by the theorem-facing Chapter 10 variance wrapper. -/
def BootstrapUniformSquareTail
    (μ : Measure Ω) (Pstar : ℕ → Ω → Measure Ωs)
    (Zstar : ℕ → Ω → Ωs → ℝ) (ν : Measure Ωlim) (Z : Ωlim → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
    (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
      (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
    Tendsto
      (fun n =>
        μ {ω |
          ε ≤ dist
            (∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
            0})
      atTop (𝓝 0)

theorem integrable_tail_sq_indicator_of_memLp
    {α : Type*} [MeasurableSpace α] {P : Measure α}
    {Y : α → ℝ} (hY : MemLp Y 2 P) (R : ℝ) :
    Integrable
      (Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2)) P := by
  have htail_null : NullMeasurableSet {ω | R ≤ |Y ω|} P :=
    nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable
        hY.aestronglyMeasurable.aemeasurable)
  exact hY.integrable_sq.indicator₀ htail_null

private theorem integral_tail_sq_eq_zero_of_abs_le_lt
    {α : Type*} [MeasurableSpace α] {P : Measure α}
    {Y : α → ℝ} {C R : ℝ}
    (hY : ∀ x, |Y x| ≤ C) (hCR : C < R) :
    (∫ x, Set.indicator {x | R ≤ |Y x|} (fun x => (Y x) ^ 2) x ∂P) = 0 := by
  have hfun :
      (fun x => Set.indicator {x | R ≤ |Y x|} (fun x => (Y x) ^ 2) x) =
        fun _ => 0 := by
    funext x
    have hnot : x ∉ {x | R ≤ |Y x|} :=
      not_le_of_gt ((hY x).trans_lt hCR)
    rw [Set.indicator_of_notMem hnot]
  simp [hfun]

/-- Fourth-moment domination of a scalar squared tail.

For `R > 0`, the tail identity
`Y² 1{|Y| ≥ R} ≤ R⁻² Y⁴` gives the conditional tail bound used to discharge
Hansen's uniform square-tail premise from a fourth-moment calculation. -/
private theorem integral_tail_sq_le_inv_sq_mul_integral_fourth
    {α : Type*} [MeasurableSpace α] {P : Measure α}
    {Y : α → ℝ} {R : ℝ} (hR : 0 < R)
    (hY4 : Integrable (fun x => (Y x) ^ 4) P) :
    (∫ x, Set.indicator {x | R ≤ |Y x|} (fun x => (Y x) ^ 2) x ∂P) ≤
      R⁻¹ ^ 2 * ∫ x, (Y x) ^ 4 ∂P := by
  have hgi : Integrable (fun x => R⁻¹ ^ 2 * (Y x) ^ 4) P :=
    hY4.const_mul _
  have hnonneg :
      0 ≤ᶠ[ae P]
        fun x => Set.indicator {x | R ≤ |Y x|} (fun x => (Y x) ^ 2) x :=
    ae_of_all P fun x =>
      Set.indicator_nonneg (fun x _ => sq_nonneg (Y x)) x
  have hle :
      (fun x => Set.indicator {x | R ≤ |Y x|} (fun x => (Y x) ^ 2) x) ≤ᶠ[ae P]
        fun x => R⁻¹ ^ 2 * (Y x) ^ 4 := by
    refine ae_of_all P fun x => ?_
    by_cases hx : R ≤ |Y x|
    · have hR_sq_le : R ^ 2 ≤ (Y x) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ hR.le hx 2
      have hYsq_nonneg : 0 ≤ (Y x) ^ 2 := sq_nonneg (Y x)
      have hmul :
          R ^ 2 * (Y x) ^ 2 ≤ (Y x) ^ 2 * (Y x) ^ 2 :=
        mul_le_mul_of_nonneg_right hR_sq_le hYsq_nonneg
      have hscale_nonneg : 0 ≤ R⁻¹ ^ 2 := sq_nonneg R⁻¹
      have hscaled :
          R⁻¹ ^ 2 * (R ^ 2 * (Y x) ^ 2) ≤
            R⁻¹ ^ 2 * ((Y x) ^ 2 * (Y x) ^ 2) :=
        mul_le_mul_of_nonneg_left hmul hscale_nonneg
      have hpoint : (Y x) ^ 2 ≤ R⁻¹ ^ 2 * (Y x) ^ 4 := by
        calc
          (Y x) ^ 2 = R⁻¹ ^ 2 * (R ^ 2 * (Y x) ^ 2) := by
            field_simp [hR.ne']
          _ ≤ R⁻¹ ^ 2 * ((Y x) ^ 2 * (Y x) ^ 2) := hscaled
          _ = R⁻¹ ^ 2 * (Y x) ^ 4 := by ring
      have hxmem : x ∈ {x | R ≤ |Y x|} := hx
      simpa [Set.indicator_of_mem hxmem] using hpoint
    · have htail_zero :
          Set.indicator {x | R ≤ |Y x|} (fun x => (Y x) ^ 2) x = 0 :=
        by simp [Set.indicator, hx]
      have hfour_nonneg : 0 ≤ (Y x) ^ 4 := by
        nlinarith [sq_nonneg ((Y x) ^ 2)]
      have hright_nonneg : 0 ≤ R⁻¹ ^ 2 * (Y x) ^ 4 :=
        mul_nonneg (sq_nonneg R⁻¹) hfour_nonneg
      simpa [htail_zero] using hright_nonneg
  calc
    (∫ x, Set.indicator {x | R ≤ |Y x|} (fun x => (Y x) ^ 2) x ∂P) ≤
        ∫ x, R⁻¹ ^ 2 * (Y x) ^ 4 ∂P :=
      integral_mono_of_nonneg hnonneg hgi hle
    _ = R⁻¹ ^ 2 * ∫ x, (Y x) ^ 4 ∂P := by
      rw [integral_const_mul]

/-- Finite normalized one-draw Lindeberg bound for Hansen Theorem 10.4.

For the ordinary `Fin (n+1)` empirical law, the conditional Lindeberg tail of
the `sqrt (n+1)`-normalized one-draw summand is bounded by `ε^{-2}` times the
scaled empirical fourth moment. This is the finite inequality used before the
shifted Marcinkiewicz step sends the right side to zero in probability. -/
private theorem lindeberg_norm_sq_tail_normalized_uniformOn_finSucc_le_scaled_fourth
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : Fin (n + 1) → E) {ε : ℝ} (hε : 0 < ε) :
    ((n + 1 : ℕ) : ℝ) *
        ∫ i : Fin (n + 1),
          Set.indicator
            {i | ε ≤ ‖((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) • Y i‖}
            (fun i => ‖((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) • Y i‖ ^ 2) i
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1))) ≤
      ε⁻¹ ^ 2 *
        (((n + 1 : ℕ) : ℝ)⁻¹ *
          ∫ i : Fin (n + 1), ‖Y i‖ ^ 4
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))) := by
  let P : Measure (Fin (n + 1)) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let c : ℝ := (Real.sqrt N)⁻¹
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hNnonneg : 0 ≤ N := hNpos.le
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (Real.sqrt_nonneg N)
  have htail :
      ∫ i : Fin (n + 1),
          Set.indicator {i | ε ≤ ‖c • Y i‖}
            (fun i => ‖c • Y i‖ ^ 2) i ∂P ≤
        ε⁻¹ ^ 2 * ∫ i : Fin (n + 1), ‖c • Y i‖ ^ 4 ∂P := by
    have hfourth_int :
        Integrable (fun i : Fin (n + 1) => ‖c • Y i‖ ^ 4) P :=
      Integrable.of_finite
    have hbase :=
      integral_tail_sq_le_inv_sq_mul_integral_fourth
        (P := P) (Y := fun i : Fin (n + 1) => ‖c • Y i‖)
        hε hfourth_int
    simpa only [abs_of_nonneg (norm_nonneg _)] using hbase
  have hscaled :
      ∫ i : Fin (n + 1), ‖c • Y i‖ ^ 4 ∂P =
        c ^ 4 * ∫ i : Fin (n + 1), ‖Y i‖ ^ 4 ∂P := by
    have hfun :
        (fun i : Fin (n + 1) => ‖c • Y i‖ ^ 4) =
          fun i : Fin (n + 1) => c ^ 4 * ‖Y i‖ ^ 4 := by
      funext i
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
      ring
    rw [hfun, integral_const_mul]
  have hc4 : c ^ 4 = N⁻¹ ^ 2 := by
    have hsqrt_sq : (Real.sqrt N) ^ 2 = N :=
      Real.sq_sqrt hNnonneg
    have hsqrt4 : (Real.sqrt N) ^ 4 = N ^ 2 := by
      calc
        (Real.sqrt N) ^ 4 = ((Real.sqrt N) ^ 2) ^ 2 := by ring
        _ = N ^ 2 := by rw [hsqrt_sq]
    calc
      c ^ 4 = ((Real.sqrt N) ^ 4)⁻¹ := by simp [c, inv_pow]
      _ = (N ^ 2)⁻¹ := by rw [hsqrt4]
      _ = N⁻¹ ^ 2 := by simp [inv_pow]
  change
    N *
        ∫ i : Fin (n + 1),
          Set.indicator {i | ε ≤ ‖c • Y i‖}
            (fun i => ‖c • Y i‖ ^ 2) i ∂P ≤
      ε⁻¹ ^ 2 * (N⁻¹ * ∫ i : Fin (n + 1), ‖Y i‖ ^ 4 ∂P)
  calc
    N *
        ∫ i : Fin (n + 1),
          Set.indicator {i | ε ≤ ‖c • Y i‖}
            (fun i => ‖c • Y i‖ ^ 2) i ∂P
        ≤ N * (ε⁻¹ ^ 2 * ∫ i : Fin (n + 1), ‖c • Y i‖ ^ 4 ∂P) :=
          mul_le_mul_of_nonneg_left htail hNnonneg
    _ = ε⁻¹ ^ 2 * (N⁻¹ * ∫ i : Fin (n + 1), ‖Y i‖ ^ 4 ∂P) := by
      rw [hscaled, hc4]
      field_simp [hNpos.ne']

/-- Lindeberg tail convergence for the normalized ordinary-bootstrap one-draw
summands in Hansen Theorem 10.4.

The finite Lindeberg inequality reduces the tail term to the scaled empirical
fourth moment. The shifted Marcinkiewicz bridge then sends that right side to
zero in probability under finite second moments and identical distribution. -/
private theorem
    lindeberg_norm_sq_tail_normalized_uniformOn_finSucc_tendsto_zero_of_identDistrib_memLp_two
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → E)
    (hY : MemLp (Y 0) 2 μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    TendstoInMeasure μ
      (fun n ω =>
        ((n + 1 : ℕ) : ℝ) *
          ∫ i : Fin (n + 1),
            Set.indicator
              {i | ε ≤
                ‖((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) • Y i.val ω‖}
              (fun i =>
                ‖((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) • Y i.val ω‖ ^ 2) i
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
      atTop (fun _ => 0) := by
  have hfourth :=
    scaled_integral_norm_fourth_uniformOn_finSucc_tendsto_zero_of_identDistrib_memLp_two
      (μ := μ) Y hY hident
  have hbound_tendsto :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) (ε⁻¹ ^ 2) hfourth
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hbound_tendsto
  · intro n ω
    exact mul_nonneg (Nat.cast_nonneg _)
      (integral_nonneg fun i =>
        Set.indicator_nonneg
          (fun i _ =>
            sq_nonneg
              (‖((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) • Y i.val ω‖)) i)
  · intro n ω
    exact
      lindeberg_norm_sq_tail_normalized_uniformOn_finSucc_le_scaled_fourth
        (Y := fun i : Fin (n + 1) => Y i.val ω) hε

private theorem inv_sq_mul_add_one_lt_of_div_add_one_le
    {B ε R : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hRlarge : (B + 1) / ε + 1 ≤ R) :
    R⁻¹ ^ 2 * (B + 1) < ε := by
  have hB1pos : 0 < B + 1 := by linarith
  have hRpos : 0 < R := by
    have hlarge_pos : 0 < (B + 1) / ε + 1 := by positivity
    exact hlarge_pos.trans_le hRlarge
  have hRgt : (B + 1) / ε < R := by linarith
  have hB_lt_mul : B + 1 < ε * R := by
    have h := (div_lt_iff₀ hε).mp hRgt
    linarith
  have hR_one : 1 ≤ R := by
    have hlarge_one : 1 ≤ (B + 1) / ε + 1 := by
      have hdiv_nonneg : 0 ≤ (B + 1) / ε := div_nonneg hB1pos.le hε.le
      linarith
    exact hlarge_one.trans hRlarge
  have hR_le_sq : R ≤ R ^ 2 := by
    simpa using Bound.le_self_pow_of_pos hR_one (by norm_num : 0 < 2)
  have hmul_le_sq : ε * R ≤ ε * R ^ 2 :=
    mul_le_mul_of_nonneg_left hR_le_sq hε.le
  have hB_lt_sq : B + 1 < ε * R ^ 2 := hB_lt_mul.trans_le hmul_le_sq
  have hdiv_lt : (B + 1) / R ^ 2 < ε := by
    rw [div_lt_iff₀ (sq_pos_of_pos hRpos)]
    nlinarith
  simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using hdiv_lt

/-- Uniform square-tail constructor from a convergent dominating moment.

The usual fourth-moment constructor is the special case where
`M n ω = ∫ Z*⁴ dP*`.  This more flexible form is useful when a linear map or
Taylor bound dominates the conditional squared tail by a different moment
sequence that has a finite probability limit. -/
theorem bootstrapUniformSquareTail_of_tail_sq_le_tendstoInMeasure
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {M : ℕ → Ω → ℝ} {B : ℝ}
    (hMoment : TendstoInMeasure μ M atTop (fun _ => B))
    (hTailLe : ∀ n ω R, 1 ≤ R →
      (∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω) ≤
        R⁻¹ ^ 2 * M n ω)
    (hChoose :
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
        R⁻¹ ^ 2 * (B + 1) < ε ∧
        (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
          (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    BootstrapUniformSquareTail μ Pstar Zstar ν Z := by
  intro ε hε
  obtain ⟨R, hR, hRbound, hlimTail⟩ := hChoose ε hε
  refine ⟨R, hR, hlimTail, ?_⟩
  have hMomentTail :
      Tendsto
        (fun n => μ {ω | 1 ≤ dist (M n ω) B})
        atTop (𝓝 0) := by
    simpa using (tendstoInMeasure_iff_dist.mp hMoment) 1 (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hMomentTail (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let tailSq : ℝ :=
    ∫ ωs,
      Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
        (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
  have htailSq_nonneg : 0 ≤ tailSq := by
    dsimp [tailSq]
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
  have htail_large : ε ≤ tailSq := by
    simpa [Real.dist_eq, tailSq, abs_of_nonneg htailSq_nonneg] using hω
  by_contra hsmall_not
  have hsmall : dist (M n ω) B < 1 := not_le.mp hsmall_not
  have hM_lt : M n ω < B + 1 := by
    rw [Real.dist_eq] at hsmall
    have hle_abs : M n ω - B ≤ |M n ω - B| := le_abs_self _
    linarith
  have hscale_nonneg : 0 ≤ R⁻¹ ^ 2 := sq_nonneg R⁻¹
  have htail_lt : tailSq < ε := by
    have hmul_le :
        R⁻¹ ^ 2 * M n ω ≤ R⁻¹ ^ 2 * (B + 1) :=
      mul_le_mul_of_nonneg_left hM_lt.le hscale_nonneg
    exact lt_of_le_of_lt ((hTailLe n ω R hR).trans hmul_le) hRbound
  exact not_lt_of_ge htail_large htail_lt

/-- Dominating-moment uniform square-tail constructor with an eventual
limit-tail threshold premise. -/
theorem bootstrapUniformSquareTail_of_tail_sq_le_tendstoInMeasure_of_eventual_limit_tail
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {M : ℕ → Ω → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hMoment : TendstoInMeasure μ M atTop (fun _ => B))
    (hTailLe : ∀ n ω R, 1 ≤ R →
      (∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω) ≤
        R⁻¹ ^ 2 * M n ω)
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    BootstrapUniformSquareTail μ Pstar Zstar ν Z :=
  bootstrapUniformSquareTail_of_tail_sq_le_tendstoInMeasure
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    hMoment hTailLe
    (fun ε hε => by
      obtain ⟨R₀, hR₀, hlimTail⟩ := hLimitTail ε hε
      let R : ℝ := max R₀ ((B + 1) / ε + 1)
      have hR₀_le : R₀ ≤ R := le_max_left _ _
      have hRlarge : (B + 1) / ε + 1 ≤ R := le_max_right _ _
      exact ⟨R, hR₀.trans hR₀_le,
        inv_sq_mul_add_one_lt_of_div_add_one_le hB hε hRlarge,
        hlimTail R hR₀_le⟩)

/-- Dominating-moment uniform square-tail constructor with the limit-tail
premise discharged by square integrability of the weak limit. -/
theorem bootstrapUniformSquareTail_of_tail_sq_le_tendstoInMeasure_of_memLp_limit
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    {M : ℕ → Ω → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hZlim : MemLp Z 2 ν)
    (hMoment : TendstoInMeasure μ M atTop (fun _ => B))
    (hTailLe : ∀ n ω R, 1 ≤ R →
      (∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω) ≤
        R⁻¹ ^ 2 * M n ω) :
    BootstrapUniformSquareTail μ Pstar Zstar ν Z :=
  bootstrapUniformSquareTail_of_tail_sq_le_tendstoInMeasure_of_eventual_limit_tail
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (B := B) hB hMoment hTailLe
    (integral_tail_sq_eventual_le_of_memLp_two (μ := ν) hZlim)

/-- Conditional tail negligibility for a quadratic Taylor-remainder envelope.

If a scalar remainder is bounded by `ρₙ ‖T*‖²`, with `ρₙ² → 0` and the
conditional fourth moment of `T*` converging in probability, then the
conditional probability of any fixed positive remainder threshold is `oₚ(1)`.
This is the reusable Taylor/Rosenthal step feeding the compact-tail smooth
Delta-method and Theorem 10.10 variance routes. -/
theorem bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
    {d : Type*} [Fintype d]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {ρ : ℕ → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ ρ n * ‖Tstar n ω ωs‖ ^ 2})
        atTop (fun _ => 0) := by
  intro δ hδ
  have hρ :
      TendstoInMeasure μ (fun n (_ : Ω) => ρ n ^ 2) atTop
        (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) hρsq
  have hprod :
      TendstoInMeasure μ
        (fun n ω =>
          ρ n ^ 2 * ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => 0) := by
    simpa using TendstoInMeasure.mul_limits_real hρ hNormFourth
  have hscaled :
      TendstoInMeasure μ
        (fun n ω =>
          δ⁻¹ ^ 2 *
            (ρ n ^ 2 * ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω))
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) (δ⁻¹ ^ 2) hprod
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hscaled
  · intro n ω
    exact measureReal_nonneg
  · intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    let A : Set Ωs :=
      {ωs | δ ≤ ρ n * ‖Tstar n ω ωs‖ ^ 2}
    let M : Ωs → ℝ := fun ωs => ρ n ^ 2 * ‖Tstar n ω ωs‖ ^ 4
    let C : ℝ :=
      δ⁻¹ ^ 2 *
        (ρ n ^ 2 * ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
    let Bset : Set Ωs := {ωs | δ ^ 2 ≤ M ωs}
    have hAB : A ⊆ Bset := by
      intro ωs hωs
      have hsq :=
        pow_le_pow_left₀ hδ.le hωs 2
      have htarget :
          δ ^ 2 ≤ ρ n ^ 2 * ‖Tstar n ω ωs‖ ^ 4 := by
        calc
          δ ^ 2 ≤ (ρ n * ‖Tstar n ω ωs‖ ^ 2) ^ 2 := hsq
          _ = ρ n ^ 2 * ‖Tstar n ω ωs‖ ^ 4 := by ring
      simpa [A, Bset, M] using htarget
    have hA_le_B : (Pstar n ω).real A ≤ (Pstar n ω).real Bset :=
      measureReal_mono hAB
    have hM_nonneg : 0 ≤ᵐ[Pstar n ω] M := by
      exact ae_of_all _ fun ωs =>
        mul_nonneg (sq_nonneg (ρ n))
          (by nlinarith [sq_nonneg (‖Tstar n ω ωs‖ ^ 2)])
    have hM_int : Integrable M (Pstar n ω) := by
      exact (hNormFourthInt n ω).const_mul (ρ n ^ 2)
    have hmarkov :
        δ ^ 2 * (Pstar n ω).real Bset ≤ ∫ ωs, M ωs ∂Pstar n ω := by
      simpa [Bset] using
        (mul_meas_ge_le_integral_of_nonneg
          (μ := Pstar n ω) (f := M) hM_nonneg hM_int (δ ^ 2))
    have hB_le :
        (Pstar n ω).real Bset ≤ (δ ^ 2)⁻¹ * ∫ ωs, M ωs ∂Pstar n ω :=
      (le_inv_mul_iff₀ (sq_pos_of_pos hδ)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov)
    calc
      (Pstar n ω).real A ≤ (Pstar n ω).real Bset := hA_le_B
      _ ≤ (δ ^ 2)⁻¹ * ∫ ωs, M ωs ∂Pstar n ω := hB_le
      _ = C := by
        rw [integral_const_mul]
        dsimp [C, M]
        rw [inv_pow]

/-- Indexed version of
`bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound`. -/
theorem bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
    {d : Type*} [Fintype d]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {ρ : ℕ → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ ρ n * ‖Tstar n ω ωs‖ ^ 2})
        atTop (fun _ => 0) := by
  intro δ hδ
  have hρ :
      TendstoInMeasure μ (fun n (_ : Ω) => ρ n ^ 2) atTop
        (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) hρsq
  have hprod :
      TendstoInMeasure μ
        (fun n ω =>
          ρ n ^ 2 * ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => 0) := by
    simpa using TendstoInMeasure.mul_limits_real hρ hNormFourth
  have hscaled :
      TendstoInMeasure μ
        (fun n ω =>
          δ⁻¹ ^ 2 *
            (ρ n ^ 2 * ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω))
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) (δ⁻¹ ^ 2) hprod
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hscaled
  · intro n ω
    exact measureReal_nonneg
  · intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    let A : Set (Ωboot n) :=
      {ωs | δ ≤ ρ n * ‖Tstar n ω ωs‖ ^ 2}
    let M : Ωboot n → ℝ := fun ωs => ρ n ^ 2 * ‖Tstar n ω ωs‖ ^ 4
    let C : ℝ :=
      δ⁻¹ ^ 2 *
        (ρ n ^ 2 * ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
    let Bset : Set (Ωboot n) := {ωs | δ ^ 2 ≤ M ωs}
    have hAB : A ⊆ Bset := by
      intro ωs hωs
      have hsq :=
        pow_le_pow_left₀ hδ.le hωs 2
      have htarget :
          δ ^ 2 ≤ ρ n ^ 2 * ‖Tstar n ω ωs‖ ^ 4 := by
        calc
          δ ^ 2 ≤ (ρ n * ‖Tstar n ω ωs‖ ^ 2) ^ 2 := hsq
          _ = ρ n ^ 2 * ‖Tstar n ω ωs‖ ^ 4 := by ring
      simpa [A, Bset, M] using htarget
    have hA_le_B : (Pstar n ω).real A ≤ (Pstar n ω).real Bset :=
      measureReal_mono hAB
    have hM_nonneg : 0 ≤ᵐ[Pstar n ω] M := by
      exact ae_of_all _ fun ωs =>
        mul_nonneg (sq_nonneg (ρ n))
          (by nlinarith [sq_nonneg (‖Tstar n ω ωs‖ ^ 2)])
    have hM_int : Integrable M (Pstar n ω) := by
      exact (hNormFourthInt n ω).const_mul (ρ n ^ 2)
    have hmarkov :
        δ ^ 2 * (Pstar n ω).real Bset ≤ ∫ ωs, M ωs ∂Pstar n ω := by
      simpa [Bset] using
        (mul_meas_ge_le_integral_of_nonneg
          (μ := Pstar n ω) (f := M) hM_nonneg hM_int (δ ^ 2))
    have hB_le :
        (Pstar n ω).real Bset ≤ (δ ^ 2)⁻¹ * ∫ ωs, M ωs ∂Pstar n ω :=
      (le_inv_mul_iff₀ (sq_pos_of_pos hδ)).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov)
    calc
      (Pstar n ω).real A ≤ (Pstar n ω).real Bset := hA_le_B
      _ ≤ (δ ^ 2)⁻¹ * ∫ ωs, M ωs ∂Pstar n ω := hB_le
      _ = C := by
        rw [integral_const_mul]
        dsimp [C, M]
        rw [inv_pow]

/-- Hansen Theorem 10.6 compact-range Gaussian Delta-method wrapper from a
quadratic remainder envelope and conditional norm fourth-moment convergence of
the linearized bootstrap statistic. -/
theorem chapter10_delta_method_gaussian_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_delta_method_gaussian_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Hansen Theorem 10.6 compact-range Gaussian Delta-method event-probability
wrapper from a quadratic remainder envelope. -/
theorem chapter10_delta_method_gaussian_event_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hA hfrontier

/-- Hansen Theorem 10.6 compact-range Gaussian Delta-method CDF wrapper from a
quadratic remainder envelope. -/
theorem
    chapter10_delta_method_gaussian_distribution_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hfrontier

/-- Hansen Theorem 10.6 compact-range Gaussian Delta-method CDF wrapper from a
quadratic remainder envelope and positive definite transformed covariance. -/
theorem
    chapter10_delta_method_gaussian_distribution_of_compact_range_quadratic_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hGVG hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Indexed Hansen Theorem 10.6 compact-range Gaussian Delta-method wrapper
from a quadratic remainder envelope and indexed conditional norm fourth-moment
convergence. -/
theorem chapter10_indexed_delta_method_gaussian_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Indexed Hansen Theorem 10.6 compact-range Gaussian Delta-method
event-probability wrapper from a quadratic remainder envelope. -/
theorem
    chapter10_indexed_delta_method_gaussian_event_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_event_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hA hfrontier

/-- Indexed Hansen Theorem 10.6 compact-range Gaussian Delta-method CDF wrapper
from a quadratic remainder envelope. -/
theorem
    chapter10_indexed_delta_method_distribution_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hfrontier

/-- Indexed Hansen Theorem 10.6 compact-range Gaussian Delta-method CDF wrapper
from a quadratic remainder envelope and positive definite transformed
covariance. -/
theorem
    chapter10_indexed_delta_method_distribution_of_compact_range_quadratic_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hGVG hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Hansen Theorem 10.6 Gaussian Delta-method wrapper from a quadratic
remainder envelope and conditional norm fourth-moment convergence of the
linearized bootstrap statistic. -/
theorem chapter10_delta_method_gaussian_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_delta_method_gaussian_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Hansen Theorem 10.6 Gaussian Delta-method event-probability wrapper from
a quadratic remainder envelope. -/
theorem chapter10_delta_method_gaussian_event_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hA hfrontier

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a quadratic
remainder envelope. -/
theorem
    chapter10_delta_method_gaussian_distribution_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hfrontier

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a quadratic
remainder envelope and positive definite transformed covariance. -/
theorem chapter10_delta_method_gaussian_distribution_of_quadratic_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hGVG hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method wrapper from a quadratic
remainder envelope and indexed conditional norm fourth-moment convergence. -/
theorem chapter10_indexed_delta_method_gaussian_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method event-probability
wrapper from a quadratic remainder envelope. -/
theorem chapter10_indexed_delta_method_gaussian_event_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_event_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hA hfrontier

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a
quadratic remainder envelope. -/
theorem
    chapter10_indexed_delta_method_gaussian_distribution_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hfrontier

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a
quadratic remainder envelope and positive definite transformed covariance. -/
theorem
    chapter10_indexed_delta_method_gaussian_distribution_of_quadratic_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hGVG hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Hansen Theorem 10.7 smooth-function Gaussian wrapper from a quadratic
Taylor-remainder envelope and conditional norm fourth-moment convergence of
the linearized bootstrap statistic. -/
theorem chapter10_smooth_gaussian_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Hansen Theorem 10.7 smooth-function Gaussian event-probability wrapper
from a quadratic Taylor-remainder envelope. -/
theorem chapter10_smooth_gaussian_event_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_smooth_function_gaussian_event_probability_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hA hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a quadratic
Taylor-remainder envelope. -/
theorem
    chapter10_smooth_gaussian_distribution_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a quadratic
Taylor-remainder envelope and positive definite transformed covariance. -/
theorem chapter10_smooth_gaussian_distribution_of_quadratic_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_tail_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hGVG hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian wrapper from a
quadratic Taylor-remainder envelope and indexed conditional norm fourth-moment
convergence. -/
theorem chapter10_indexed_smooth_gaussian_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian event-probability
wrapper from a quadratic Taylor-remainder envelope. -/
theorem chapter10_indexed_smooth_gaussian_event_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_smooth_gaussian_event_probability_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hA hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a
quadratic Taylor-remainder envelope. -/
theorem
    chapter10_indexed_smooth_gaussian_distribution_of_quadratic_remainder_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_smooth_gaussian_distribution_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a
quadratic Taylor-remainder envelope and positive definite transformed
covariance. -/
theorem
    chapter10_indexed_smooth_gaussian_distribution_of_quadratic_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_smooth_gaussian_distribution_of_compact_tail_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hGVG hT hPstar hTstar hthetaStar hTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Hansen Theorem 10.7 compact-range smooth-function Gaussian wrapper from a
quadratic Taylor-remainder envelope and conditional norm fourth-moment
convergence of the linearized bootstrap statistic. -/
theorem chapter10_smooth_gaussian_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_smooth_function_gaussian_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Hansen Theorem 10.7 compact-range smooth-function Gaussian
event-probability wrapper from a quadratic Taylor-remainder envelope. -/
theorem chapter10_smooth_gaussian_event_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_smooth_function_gaussian_event_probability_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hA hfrontier

/-- Hansen Theorem 10.7 compact-range smooth-function Gaussian CDF wrapper
from a quadratic Taylor-remainder envelope. -/
theorem
    chapter10_smooth_gaussian_distribution_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hfrontier

/-- Hansen Theorem 10.7 compact-range smooth-function Gaussian CDF wrapper
from a quadratic Taylor-remainder envelope and positive definite transformed
covariance. -/
theorem chapter10_smooth_gaussian_distribution_of_compact_range_quadratic_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_range_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hGVG hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Indexed Hansen Theorem 10.7 compact-range smooth-function Gaussian wrapper
from a quadratic Taylor-remainder envelope and indexed conditional norm
fourth-moment convergence. -/
theorem chapter10_indexed_smooth_gaussian_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Indexed Hansen Theorem 10.7 compact-range smooth-function Gaussian
event-probability wrapper from a quadratic Taylor-remainder envelope. -/
theorem
    chapter10_indexed_smooth_gaussian_event_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_smooth_gaussian_event_probability_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hA hfrontier

/-- Indexed Hansen Theorem 10.7 compact-range smooth-function Gaussian CDF
wrapper from a quadratic Taylor-remainder envelope. -/
theorem
    chapter10_indexed_smooth_gaussian_distribution_of_compact_range_quadratic_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hfrontier

/-- Indexed Hansen Theorem 10.7 compact-range smooth-function Gaussian CDF
wrapper from a quadratic Taylor-remainder envelope and positive definite
transformed covariance. -/
theorem
    chapter10_indexed_smooth_gaussian_distribution_of_compact_range_quadratic_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ} {BT : ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hGVG hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound

/-- Uniform square-tail constructor from a fourth-moment convergence premise.

The conditional fourth moment controls the conditional squared tail by
`R⁻² E*[Z*⁴]`.  If that fourth moment converges in probability to `B`, and the
chosen threshold also makes the limit squared tail small, then Hansen's named
uniform square-tail condition follows. -/
theorem bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {B : ℝ}
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hChoose :
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
        R⁻¹ ^ 2 * (B + 1) < ε ∧
        (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
          (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    BootstrapUniformSquareTail μ Pstar Zstar ν Z := by
  intro ε hε
  obtain ⟨R, hR, hRbound, hlimTail⟩ := hChoose ε hε
  refine ⟨R, hR, hlimTail, ?_⟩
  have hFourthTail :
      Tendsto
        (fun n =>
          μ {ω | 1 ≤
            dist (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) B})
        atTop (𝓝 0) := by
    simpa using (tendstoInMeasure_iff_dist.mp hFourth) 1 (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hFourthTail (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let tailSq : ℝ :=
    ∫ ωs,
      Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
        (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
  have htailSq_nonneg : 0 ≤ tailSq := by
    dsimp [tailSq]
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
  have htail_large : ε ≤ tailSq := by
    simpa [Real.dist_eq, tailSq, abs_of_nonneg htailSq_nonneg] using hω
  by_contra hsmall_not
  have hsmall : dist (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) B < 1 :=
    not_le.mp hsmall_not
  have hfourth_lt :
      (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) < B + 1 := by
    rw [Real.dist_eq] at hsmall
    have hle_abs :
        (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) - B ≤
          |(∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) - B| :=
      le_abs_self _
    linarith
  have htail_le :
      tailSq ≤ R⁻¹ ^ 2 * ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω := by
    dsimp [tailSq]
    exact integral_tail_sq_le_inv_sq_mul_integral_fourth
      (P := Pstar n ω) (Y := Zstar n ω)
      (zero_lt_one.trans_le hR) (hFourthInt n ω)
  have hscale_nonneg : 0 ≤ R⁻¹ ^ 2 := sq_nonneg R⁻¹
  have htail_lt : tailSq < ε := by
    have hmul_le :
        R⁻¹ ^ 2 * (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) ≤
          R⁻¹ ^ 2 * (B + 1) :=
      mul_le_mul_of_nonneg_left hfourth_lt.le hscale_nonneg
    exact lt_of_le_of_lt (htail_le.trans hmul_le) hRbound
  exact not_lt_of_ge htail_large htail_lt

/-- Fourth-moment uniform square-tail constructor with an eventual limit-tail
threshold premise.

This wrapper chooses the common threshold internally: the limit-tail premise
only needs to hold for all sufficiently large thresholds, while the deterministic
`R⁻² (B + 1)` bound is made small using `B ≥ 0`. -/
theorem bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {B : ℝ}
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    BootstrapUniformSquareTail μ Pstar Zstar ν Z :=
  bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    hFourth hFourthInt
    (fun ε hε => by
      obtain ⟨R₀, hR₀, hlimTail⟩ := hLimitTail ε hε
      let R : ℝ := max R₀ ((B + 1) / ε + 1)
      have hR₀_le : R₀ ≤ R := le_max_left _ _
      have hRlarge : (B + 1) / ε + 1 ≤ R := le_max_right _ _
      exact ⟨R, hR₀.trans hR₀_le,
        inv_sq_mul_add_one_lt_of_div_add_one_le hB hε hRlarge,
        hlimTail R hR₀_le⟩)

/-- Fourth-moment uniform square-tail constructor with the limit-tail premise
discharged by square integrability of the weak limit. -/
theorem bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_memLp_limit
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    {B : ℝ}
    (hB : 0 ≤ B)
    (hZlim : MemLp Z 2 ν)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω)) :
    BootstrapUniformSquareTail μ Pstar Zstar ν Z :=
  bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (B := B) hB hFourth hFourthInt
    (integral_tail_sq_eventual_le_of_memLp_two (μ := ν) hZlim)

/-- Uniform square-tail constructor for eventually bounded conditional
bootstrap statistics.

If the bootstrap statistic is eventually bounded by a deterministic constant
and the weak limit is square-integrable, the bootstrap squared tail is
eventually identically zero above a large enough deterministic threshold, while
the limit squared tail is small by `MemLp Z 2`. -/
theorem bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    {C : ℝ}
    (hZlim : MemLp Z 2 ν)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C) :
    BootstrapUniformSquareTail μ Pstar Zstar ν Z := by
  intro ε hε
  obtain ⟨R₀, hR₀, hlimTail⟩ :=
    integral_tail_sq_eventual_le_of_memLp_two (μ := ν) hZlim ε hε
  let R : ℝ := max R₀ (C + 1)
  have hR₀_le : R₀ ≤ R := le_max_left _ _
  have hCadd_le : C + 1 ≤ R := le_max_right _ _
  have hR : 1 ≤ R := hR₀.trans hR₀_le
  have hC_lt_R : C < R := (lt_add_one C).trans_le hCadd_le
  refine ⟨R, hR, hlimTail R hR₀_le, ?_⟩
  have hsource_zero :
      (fun n =>
        μ {ω |
          ε ≤ dist
            (∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
            0}) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [hbound] with n hn
    have hset :
        {ω |
          ε ≤ dist
            (∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
            0} = ∅ := by
      ext ω
      have htail_zero :
          (∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω) = 0 :=
        integral_tail_sq_eq_zero_of_abs_le_lt
          (P := Pstar n ω) (Y := Zstar n ω) (C := C) (R := R)
          (hn ω) hC_lt_R
      simp [htail_zero, not_le_of_gt hε]
    rw [hset]
    simp
  rw [tendsto_congr' hsource_zero]
  exact tendsto_const_nhds

/-- Uniform square-tail control transfers to a statistic whose conditional
tail integrals are pointwise dominated by the original statistic's tail
integrals. -/
theorem bootstrapUniformSquareTail_of_integral_tail_sq_le
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hTail : BootstrapUniformSquareTail μ Pstar Xstar ν Z)
    (hle : ∀ n ω R,
      (∫ ωs,
        Set.indicator {ωs | R ≤ |Ystar n ω ωs|}
          (fun ωs => (Ystar n ω ωs) ^ 2) ωs ∂Pstar n ω) ≤
      ∫ ωs,
        Set.indicator {ωs | R ≤ |Xstar n ω ωs|}
          (fun ωs => (Xstar n ω ωs) ^ 2) ωs ∂Pstar n ω) :
    BootstrapUniformSquareTail μ Pstar Ystar ν Z := by
  intro ε hε
  obtain ⟨R, hR, hlimTail, hsourceTail⟩ := hTail ε hε
  refine ⟨R, hR, hlimTail, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hsourceTail (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let yTail : ℝ :=
    ∫ ωs,
      Set.indicator {ωs | R ≤ |Ystar n ω ωs|}
        (fun ωs => (Ystar n ω ωs) ^ 2) ωs ∂Pstar n ω
  let xTail : ℝ :=
    ∫ ωs,
      Set.indicator {ωs | R ≤ |Xstar n ω ωs|}
        (fun ωs => (Xstar n ω ωs) ^ 2) ωs ∂Pstar n ω
  have hy_nonneg : 0 ≤ yTail := by
    dsimp [yTail]
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun x _ => sq_nonneg (Ystar n ω x)) ωs
  have hx_nonneg : 0 ≤ xTail := by
    dsimp [xTail]
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun x _ => sq_nonneg (Xstar n ω x)) ωs
  have hy_large : ε ≤ yTail := by
    simpa [Real.dist_eq, yTail, abs_of_nonneg hy_nonneg] using hω
  have hxy : yTail ≤ xTail := by
    simpa [xTail, yTail] using hle n ω R
  have hx_large : ε ≤ xTail := hy_large.trans hxy
  simpa [Real.dist_eq, xTail, abs_of_nonneg hx_nonneg] using hx_large

/-- Hansen Theorem 10.9 conditional mean convergence from weak convergence and
uniform square-tail control.

This is one of the two conditional moment conclusions used by the variance
consistency bridge.  Squared-tail control supplies the first-moment clipping
error because thresholds are chosen at least one. -/
theorem chapter10_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstarInt : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    exact memLp_one_iff_integrable.mp ((hZmem n ω).mono_exponent one_le_two)
  have hZlimInt : Integrable Z ν :=
    memLp_one_iff_integrable.mp (hZlim.mono_exponent one_le_two)
  have hTailMeanProb : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (bootstrapMeanReal Pstar Zstar n ω -
                (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
              0})
        atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq (ε / 2) (by positivity)
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hlimAbsLe :=
        integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := ν) (Y := Z) hZlim hR_one
      have hclip :=
        abs_integral_sub_realClip_le_two_mul_integral_tail_abs
          (μ := ν) (Y := Z) hZlimInt hR_nonneg
      calc
        |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤
            2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => |Z ωlim|) ωlim ∂ν := hclip
        _ ≤ 2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := by nlinarith
        _ ≤ 2 * (ε / 2) := by nlinarith
        _ = ε := by ring
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hsourceSq (fun _ => zero_le _) ?_
      intro n
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let tailSq : ℝ :=
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
      have htailSq_nonneg : 0 ≤ tailSq := by
        dsimp [tailSq]
        exact integral_nonneg fun ωs =>
          Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
      have hboundMean :=
        bootstrapMeanReal_abs_sub_realClip_le_two_mul_integral_tail_abs
          hPstarFinite hZstarInt hR_nonneg n ω
      have htailAbsLe :
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω ≤ tailSq := by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        exact integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := Pstar n ω) (Y := Zstar n ω) (hZmem n ω) hR_one
      have hdist_mean :
          ε ≤
            |bootstrapMeanReal Pstar Zstar n ω -
              (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| := by
        simpa [Real.dist_eq] using hω
      have htail_ge : ε / 2 ≤ tailSq := by nlinarith
      simpa [tailSq, Real.dist_eq, abs_of_nonneg htailSq_nonneg] using htail_ge
  simpa [bootstrapMeanReal] using
    hweak.integral_tendsto_of_realClip_tailProb hTailMeanProb

/-- Hansen Theorem 10.9 conditional second-moment convergence from weak
convergence and uniform square-tail control.

This is the second conditional moment conclusion used by the variance
consistency bridge. -/
theorem chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hTailSecondProb : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (bootstrapSecondMomentReal Pstar Zstar n ω -
                (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
              0})
        atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq (ε / 2) (by positivity)
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hclip :=
        abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
          (μ := ν) (Y := Z) hZlim hR_nonneg
      calc
        |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
            ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤
            2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := hclip
        _ ≤ 2 * (ε / 2) := by nlinarith
        _ = ε := by ring
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hsourceSq (fun _ => zero_le _) ?_
      intro n
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let tailSq : ℝ :=
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
      have htailSq_nonneg : 0 ≤ tailSq := by
        dsimp [tailSq]
        exact integral_nonneg fun ωs =>
          Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
      have hboundSecond :=
        bootstrapSecondMomentReal_abs_sub_realClip_sq_le_two_mul_integral_tail_sq
          hPstarFinite hZmem hR_nonneg n ω
      have hdist_second :
          ε ≤
            |bootstrapSecondMomentReal Pstar Zstar n ω -
              (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| := by
        simpa [Real.dist_eq] using hω
      have htail_ge : ε / 2 ≤ tailSq := by nlinarith
      simpa [tailSq, Real.dist_eq, abs_of_nonneg htailSq_nonneg] using htail_ge
  simpa [bootstrapSecondMomentReal] using
    hweak.integral_sq_tendsto_of_realClip_tailProb hTailSecondProb

/-- Hansen Theorem 10.9 conditional mean convergence from the named
uniform-square-tail condition package. -/
theorem chapter10_bootstrap_mean_tendsto_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, Z ωlim ∂ν) :=
  chapter10_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Hansen Theorem 10.9 conditional second-moment convergence from the named
uniform-square-tail condition package. -/
theorem chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) :=
  chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Hansen Theorem 10.9, weak-distribution plus uniform-square-tail variance
bridge.

This is the theorem-facing uniform-integrability assembly: for every tolerance
one chooses a large threshold whose squared tail is small for the limit law and
small in probability for the conditional bootstrap law. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
        (fun _ => ∫ ωlim, Z ωlim ∂ν) :=
    chapter10_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailSq
  have hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) :=
    chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailSq
  exact chapter10_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZmem hmean hsecond

/-- Hansen Theorem 10.9 from a named uniform-square-tail condition.

This is the public theorem-facing wrapper: bootstrap weak convergence plus
`BootstrapUniformSquareTail` gives conditional bootstrap variance consistency. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Hansen Theorem 10.9 from fourth-moment tail controls.

Bootstrap weak convergence plus conditional fourth-moment convergence supplies
conditional bootstrap variance consistency once the weak-limit squared tails
are eventually small at large thresholds. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_tail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
    (bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (B := B) hB hFourth hFourthInt hLimitTail)

/-- Hansen Theorem 10.9 from fourth-moment convergence with the weak-limit tail
premise discharged by `MemLp Z 2 ν`. -/
theorem
    chapter10_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_memLp_limit
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
    (bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_memLp_limit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (B := B) hB hZlim hFourth hFourthInt)

/-- Hansen Theorem 10.9 from bootstrap weak convergence and an eventual
deterministic bootstrap bound.

This bounded-statistic route discharges Hansen's uniform-square-tail premise
by making the conditional bootstrap squared tail eventually zero, while
`MemLp Z 2` controls the weak-limit tail. -/
theorem
    chapter10_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
    (bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hZlim hbound)

/-- Indexed textbook-style uniform square-tail condition for Hansen Theorem
10.9.

This is the sample-size-dependent bootstrap-space version of
`BootstrapUniformSquareTail`: for every tolerance, one threshold makes the
limit squared tail small and makes the corresponding indexed conditional
bootstrap squared tail small in probability. -/
def BootstrapUniformSquareTailIndexed
    (μ : Measure Ω) {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ) (ν : Measure Ωlim)
    (Z : Ωlim → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
    (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
      (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
    Tendsto
      (fun n =>
        μ {ω |
          ε ≤ dist
            (∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
            0})
      atTop (𝓝 0)

/-- Indexed uniform square-tail constructor from a convergent dominating
moment for sample-size-dependent bootstrap spaces. -/
theorem bootstrapUniformSquareTailIndexed_of_tail_sq_le_tendstoInMeasure
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {M : ℕ → Ω → ℝ} {B : ℝ}
    (hMoment : TendstoInMeasure μ M atTop (fun _ => B))
    (hTailLe : ∀ n ω R, 1 ≤ R →
      (∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω) ≤
        R⁻¹ ^ 2 * M n ω)
    (hChoose :
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
        R⁻¹ ^ 2 * (B + 1) < ε ∧
        (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
          (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z := by
  intro ε hε
  obtain ⟨R, hR, hRbound, hlimTail⟩ := hChoose ε hε
  refine ⟨R, hR, hlimTail, ?_⟩
  have hMomentTail :
      Tendsto
        (fun n => μ {ω | 1 ≤ dist (M n ω) B})
        atTop (𝓝 0) := by
    simpa using (tendstoInMeasure_iff_dist.mp hMoment) 1 (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hMomentTail (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let tailSq : ℝ :=
    ∫ ωs,
      Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
        (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
  have htailSq_nonneg : 0 ≤ tailSq := by
    dsimp [tailSq]
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
  have htail_large : ε ≤ tailSq := by
    simpa [Real.dist_eq, tailSq, abs_of_nonneg htailSq_nonneg] using hω
  by_contra hsmall_not
  have hsmall : dist (M n ω) B < 1 := not_le.mp hsmall_not
  have hM_lt : M n ω < B + 1 := by
    rw [Real.dist_eq] at hsmall
    have hle_abs : M n ω - B ≤ |M n ω - B| := le_abs_self _
    linarith
  have hscale_nonneg : 0 ≤ R⁻¹ ^ 2 := sq_nonneg R⁻¹
  have htail_lt : tailSq < ε := by
    have hmul_le :
        R⁻¹ ^ 2 * M n ω ≤ R⁻¹ ^ 2 * (B + 1) :=
      mul_le_mul_of_nonneg_left hM_lt.le hscale_nonneg
    exact lt_of_le_of_lt ((hTailLe n ω R hR).trans hmul_le) hRbound
  exact not_lt_of_ge htail_large htail_lt

/-- Indexed dominating-moment uniform square-tail constructor with an eventual
limit-tail threshold premise. -/
theorem
    bootstrapUniformSquareTailIndexed_of_tail_sq_le_tendstoInMeasure_of_eventual_limit_tail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {M : ℕ → Ω → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hMoment : TendstoInMeasure μ M atTop (fun _ => B))
    (hTailLe : ∀ n ω R, 1 ≤ R →
      (∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω) ≤
        R⁻¹ ^ 2 * M n ω)
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z :=
  bootstrapUniformSquareTailIndexed_of_tail_sq_le_tendstoInMeasure
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    hMoment hTailLe
    (fun ε hε => by
      obtain ⟨R₀, hR₀, hlimTail⟩ := hLimitTail ε hε
      let R : ℝ := max R₀ ((B + 1) / ε + 1)
      have hR₀_le : R₀ ≤ R := le_max_left _ _
      have hRlarge : (B + 1) / ε + 1 ≤ R := le_max_right _ _
      exact ⟨R, hR₀.trans hR₀_le,
        inv_sq_mul_add_one_lt_of_div_add_one_le hB hε hRlarge,
        hlimTail R hR₀_le⟩)

/-- Indexed dominating-moment uniform square-tail constructor with the
limit-tail premise discharged by square integrability of the weak limit. -/
theorem bootstrapUniformSquareTailIndexed_of_tail_sq_le_tendstoInMeasure_of_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    {M : ℕ → Ω → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hZlim : MemLp Z 2 ν)
    (hMoment : TendstoInMeasure μ M atTop (fun _ => B))
    (hTailLe : ∀ n ω R, 1 ≤ R →
      (∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω) ≤
        R⁻¹ ^ 2 * M n ω) :
    BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z :=
  bootstrapUniformSquareTailIndexed_of_tail_sq_le_tendstoInMeasure_of_eventual_limit_tail
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (B := B) hB hMoment hTailLe
    (integral_tail_sq_eventual_le_of_memLp_two (μ := ν) hZlim)

/-- Indexed uniform square-tail constructor from a fourth-moment convergence
premise for sample-size-dependent bootstrap spaces. -/
theorem bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {B : ℝ}
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hChoose :
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
        R⁻¹ ^ 2 * (B + 1) < ε ∧
        (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
          (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z := by
  intro ε hε
  obtain ⟨R, hR, hRbound, hlimTail⟩ := hChoose ε hε
  refine ⟨R, hR, hlimTail, ?_⟩
  have hFourthTail :
      Tendsto
        (fun n =>
          μ {ω | 1 ≤
            dist (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) B})
        atTop (𝓝 0) := by
    simpa using (tendstoInMeasure_iff_dist.mp hFourth) 1 (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hFourthTail (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let tailSq : ℝ :=
    ∫ ωs,
      Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
        (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
  have htailSq_nonneg : 0 ≤ tailSq := by
    dsimp [tailSq]
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
  have htail_large : ε ≤ tailSq := by
    simpa [Real.dist_eq, tailSq, abs_of_nonneg htailSq_nonneg] using hω
  by_contra hsmall_not
  have hsmall : dist (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) B < 1 :=
    not_le.mp hsmall_not
  have hfourth_lt :
      (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) < B + 1 := by
    rw [Real.dist_eq] at hsmall
    have hle_abs :
        (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) - B ≤
          |(∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) - B| :=
      le_abs_self _
    linarith
  have htail_le :
      tailSq ≤ R⁻¹ ^ 2 * ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω := by
    dsimp [tailSq]
    exact integral_tail_sq_le_inv_sq_mul_integral_fourth
      (P := Pstar n ω) (Y := Zstar n ω)
      (zero_lt_one.trans_le hR) (hFourthInt n ω)
  have hscale_nonneg : 0 ≤ R⁻¹ ^ 2 := sq_nonneg R⁻¹
  have htail_lt : tailSq < ε := by
    have hmul_le :
        R⁻¹ ^ 2 * (∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω) ≤
          R⁻¹ ^ 2 * (B + 1) :=
      mul_le_mul_of_nonneg_left hfourth_lt.le hscale_nonneg
    exact lt_of_le_of_lt (htail_le.trans hmul_le) hRbound
  exact not_lt_of_ge htail_large htail_lt

/-- Indexed fourth-moment uniform square-tail constructor with an eventual
limit-tail threshold premise. -/
theorem
    bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {B : ℝ}
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z :=
  bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    hFourth hFourthInt
    (fun ε hε => by
      obtain ⟨R₀, hR₀, hlimTail⟩ := hLimitTail ε hε
      let R : ℝ := max R₀ ((B + 1) / ε + 1)
      have hR₀_le : R₀ ≤ R := le_max_left _ _
      have hRlarge : (B + 1) / ε + 1 ≤ R := le_max_right _ _
      exact ⟨R, hR₀.trans hR₀_le,
        inv_sq_mul_add_one_lt_of_div_add_one_le hB hε hRlarge,
        hlimTail R hR₀_le⟩)

/-- Indexed fourth-moment uniform square-tail constructor with the limit-tail
premise discharged by square integrability of the weak limit. -/
theorem
    bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    {B : ℝ}
    (hB : 0 ≤ B)
    (hZlim : MemLp Z 2 ν)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω)) :
    BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z :=
  bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (B := B) hB hFourth hFourthInt
    (integral_tail_sq_eventual_le_of_memLp_two (μ := ν) hZlim)

/-- Indexed uniform square-tail constructor for eventually bounded conditional
bootstrap statistics. -/
theorem bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    {C : ℝ}
    (hZlim : MemLp Z 2 ν)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C) :
    BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z := by
  intro ε hε
  obtain ⟨R₀, hR₀, hlimTail⟩ :=
    integral_tail_sq_eventual_le_of_memLp_two (μ := ν) hZlim ε hε
  let R : ℝ := max R₀ (C + 1)
  have hR₀_le : R₀ ≤ R := le_max_left _ _
  have hCadd_le : C + 1 ≤ R := le_max_right _ _
  have hR : 1 ≤ R := hR₀.trans hR₀_le
  have hC_lt_R : C < R := (lt_add_one C).trans_le hCadd_le
  refine ⟨R, hR, hlimTail R hR₀_le, ?_⟩
  have hsource_zero :
      (fun n =>
        μ {ω |
          ε ≤ dist
            (∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
            0}) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [hbound] with n hn
    have hset :
        {ω |
          ε ≤ dist
            (∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
            0} = ∅ := by
      ext ω
      have htail_zero :
          (∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω) = 0 :=
        integral_tail_sq_eq_zero_of_abs_le_lt
          (P := Pstar n ω) (Y := Zstar n ω) (C := C) (R := R)
          (hn ω) hC_lt_R
      simp [htail_zero, not_le_of_gt hε]
    rw [hset]
    simp
  rw [tendsto_congr' hsource_zero]
  exact tendsto_const_nhds

/-- Indexed version of
`bootstrapUniformSquareTail_of_integral_tail_sq_le`. -/
theorem bootstrapUniformSquareTailIndexed_of_integral_tail_sq_le
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Xstar ν Z)
    (hle : ∀ n ω R,
      (∫ ωs,
        Set.indicator {ωs | R ≤ |Ystar n ω ωs|}
          (fun ωs => (Ystar n ω ωs) ^ 2) ωs ∂Pstar n ω) ≤
      ∫ ωs,
        Set.indicator {ωs | R ≤ |Xstar n ω ωs|}
          (fun ωs => (Xstar n ω ωs) ^ 2) ωs ∂Pstar n ω) :
    BootstrapUniformSquareTailIndexed μ Pstar Ystar ν Z := by
  intro ε hε
  obtain ⟨R, hR, hlimTail, hsourceTail⟩ := hTail ε hε
  refine ⟨R, hR, hlimTail, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hsourceTail (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let yTail : ℝ :=
    ∫ ωs,
      Set.indicator {ωs | R ≤ |Ystar n ω ωs|}
        (fun ωs => (Ystar n ω ωs) ^ 2) ωs ∂Pstar n ω
  let xTail : ℝ :=
    ∫ ωs,
      Set.indicator {ωs | R ≤ |Xstar n ω ωs|}
        (fun ωs => (Xstar n ω ωs) ^ 2) ωs ∂Pstar n ω
  have hy_nonneg : 0 ≤ yTail := by
    dsimp [yTail]
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun x _ => sq_nonneg (Ystar n ω x)) ωs
  have hx_nonneg : 0 ≤ xTail := by
    dsimp [xTail]
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun x _ => sq_nonneg (Xstar n ω x)) ωs
  have hy_large : ε ≤ yTail := by
    simpa [Real.dist_eq, yTail, abs_of_nonneg hy_nonneg] using hω
  have hxy : yTail ≤ xTail := by
    simpa [xTail, yTail] using hle n ω R
  have hx_large : ε ≤ xTail := hy_large.trans hxy
  simpa [Real.dist_eq, xTail, abs_of_nonneg hx_nonneg] using hx_large

/-- Indexed Hansen Theorem 10.9 conditional mean convergence from weak
convergence and uniform square-tail control. -/
theorem chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstarInt : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    exact memLp_one_iff_integrable.mp ((hZmem n ω).mono_exponent one_le_two)
  have hZlimInt : Integrable Z ν :=
    memLp_one_iff_integrable.mp (hZlim.mono_exponent one_le_two)
  have hTailMeanProb : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (bootstrapMeanRealIndexed Pstar Zstar n ω -
                (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
              0})
        atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq (ε / 2) (by positivity)
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hlimAbsLe :=
        integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := ν) (Y := Z) hZlim hR_one
      have hclip :=
        abs_integral_sub_realClip_le_two_mul_integral_tail_abs
          (μ := ν) (Y := Z) hZlimInt hR_nonneg
      calc
        |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤
            2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => |Z ωlim|) ωlim ∂ν := hclip
        _ ≤ 2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := by nlinarith
        _ ≤ 2 * (ε / 2) := by nlinarith
        _ = ε := by ring
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hsourceSq (fun _ => zero_le _) ?_
      intro n
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let tailSq : ℝ :=
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
      have htailSq_nonneg : 0 ≤ tailSq := by
        dsimp [tailSq]
        exact integral_nonneg fun ωs =>
          Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
      have hboundMean :
          |bootstrapMeanRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| ≤
            2 * ∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        simpa [bootstrapMeanRealIndexed] using
          abs_integral_sub_realClip_le_two_mul_integral_tail_abs
            (μ := Pstar n ω) (Y := Zstar n ω) (hZstarInt n ω) hR_nonneg
      have htailAbsLe :
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω ≤ tailSq := by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        exact integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := Pstar n ω) (Y := Zstar n ω) (hZmem n ω) hR_one
      have hdist_mean :
          ε ≤
            |bootstrapMeanRealIndexed Pstar Zstar n ω -
              (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| := by
        simpa [Real.dist_eq] using hω
      have htail_ge : ε / 2 ≤ tailSq := by nlinarith
      simpa [tailSq, Real.dist_eq, abs_of_nonneg htailSq_nonneg] using htail_ge
  simpa [bootstrapMeanRealIndexed] using
    hweak.integral_tendsto_of_realClip_tailProb hTailMeanProb

/-- Indexed Hansen Theorem 10.9 conditional second-moment convergence from
weak convergence and uniform square-tail control. -/
theorem chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hTailSecondProb : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
                (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
              0})
        atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq (ε / 2) (by positivity)
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hclip :=
        abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
          (μ := ν) (Y := Z) hZlim hR_nonneg
      calc
        |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
            ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤
            2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := hclip
        _ ≤ 2 * (ε / 2) := by nlinarith
        _ = ε := by ring
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hsourceSq (fun _ => zero_le _) ?_
      intro n
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let tailSq : ℝ :=
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
      have htailSq_nonneg : 0 ≤ tailSq := by
        dsimp [tailSq]
        exact integral_nonneg fun ωs =>
          Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
      have hboundSecond :
          |bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| ≤
            2 * ∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        simpa [bootstrapSecondMomentRealIndexed] using
          abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
            (μ := Pstar n ω) (Y := Zstar n ω) (hZmem n ω) hR_nonneg
      have hdist_second :
          ε ≤
            |bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
              (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| := by
        simpa [Real.dist_eq] using hω
      have htail_ge : ε / 2 ≤ tailSq := by nlinarith
      simpa [tailSq, Real.dist_eq, abs_of_nonneg htailSq_nonneg] using htail_ge
  simpa [bootstrapSecondMomentRealIndexed] using
    hweak.integral_sq_tendsto_of_realClip_tailProb hTailSecondProb

/-- Indexed Hansen Theorem 10.9 conditional mean convergence from the named
uniform-square-tail condition package. -/
theorem chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, Z ωlim ∂ν) :=
  chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Indexed Hansen Theorem 10.9 conditional second-moment convergence from the
named uniform-square-tail condition package. -/
theorem chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) :=
  chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Indexed Hansen Theorem 10.9, weak-distribution plus uniform-square-tail
variance bridge. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => ∫ ωlim, Z ωlim ∂ν) :=
    chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailSq
  have hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) :=
    chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailSq
  exact chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZmem hmean hsecond

/-- Indexed Hansen Theorem 10.9 from a named uniform-square-tail condition. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Indexed Hansen Theorem 10.9 from fourth-moment tail controls. -/
theorem
    chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
    (bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (B := B) hB hFourth hFourthInt hLimitTail)

/-- Indexed Hansen Theorem 10.9 from fourth-moment convergence with the
weak-limit tail premise discharged by `MemLp Z 2 ν`. -/
theorem
    chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
    (bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_memLp_limit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (B := B) hB hZlim hFourth hFourthInt)

/-- Indexed ordinary-bootstrap uniform-square-tail route from Hansen's
fourth-moment cumulant formula.

For the concrete `Fin (n+1)` ordinary resampling space, convergence of the
empirical variance and negligibility of the scaled fourth cumulant supply the
conditional fourth-moment premise in the indexed uniform-square-tail
constructor. -/
theorem
    bootstrapUniformSquareTailIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_of_cumulants
    [IsFiniteMeasure ν]
    (Y : ℕ → Ω → ℝ) {Z : Ωlim → ℝ} {σ2 : ℝ}
    (hZlim : MemLp Z 2 ν)
    (hCumulant2 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => σ2))
    (hScaledCumulant4 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant4 (fun i : Fin (n + 1) => Y i.val ω) /
            (n + 1 : ℝ))
        atTop (fun _ => 0)) :
    BootstrapUniformSquareTailIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
      ν Z := by
  have hB : 0 ≤ 3 * σ2 ^ 2 := by
    nlinarith [sq_nonneg σ2]
  have hFourth :=
    integral_fourth_normalized_finSucc_resampleMean_sub_empiricalMean_tendstoInMeasure_of_cumulants
      (μ := μ) (Y := Y) hCumulant2 hScaledCumulant4
  exact
    bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_memLp_limit
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Zstar := fun n ω ωs =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
      (ν := ν) (Z := Z) (B := 3 * σ2 ^ 2)
      hB hZlim hFourth
      (fun n ω => Integrable.of_finite)

/-- Indexed Hansen Theorem 10.9 for the concrete ordinary bootstrap sample
mean, using Hansen's fourth-moment cumulant formula to discharge uniform square
integrability.

This is the sample-mean fourth-moment route behind equation (10.17): once the
ordinary normalized bootstrap mean has the indexed weak limit and the empirical
cumulants satisfy the exact-formula convergence premises, the conditional
bootstrap variance is consistent. -/
theorem
    chapter10_indexed_bootstrap_variance_finSucc_resampleMean_of_weak_distribution_cumulants
    [IsFiniteMeasure ν]
    (Y : ℕ → Ω → ℝ) {Z : Ωlim → ℝ} {σ2 : ℝ}
    (hZlim : MemLp Z 2 ν)
    (hweak :
      TendstoInBootstrapWeakDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
        ν Z)
    (hCumulant2 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => σ2))
    (hScaledCumulant4 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant4 (fun i : Fin (n + 1) => Y i.val ω) /
            (n + 1 : ℝ))
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))))
      atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hPstar :
      ∀ n (_ω : Ω),
        IsProbabilityMeasure
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))) := by
    intro n _ω
    infer_instance
  have hZmem :
      ∀ n ω,
        MemLp
          (fun ωs : Fin (n + 1) → Fin (n + 1) =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
          2
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    exact memLp_two_uniformOn_univ
      (Y := fun ωs : Fin (n + 1) → Fin (n + 1) =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
  have hTail :
      BootstrapUniformSquareTailIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
        ν Z :=
    bootstrapUniformSquareTailIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_of_cumulants
      (μ := μ) (ν := ν) (Y := Y) (Z := Z) hZlim hCumulant2
      hScaledCumulant4
  exact
    chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Indexed Hansen Theorem 10.9 from bootstrap weak convergence and an
eventual deterministic bootstrap bound. -/
theorem
    chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ} {C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
    (bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hZlim hbound)

/-- Coordinate norm bound for a matrix-linear map between Euclidean spaces. -/
theorem abs_matrixContinuousLinearMap_coord_le_opNorm_mul_norm
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    (G : Matrix r d ℝ) (a : r) (x : EuclideanSpace ℝ d) :
    |(((matrixContinuousLinearMap G x : EuclideanSpace ℝ r) : r → ℝ) a)| ≤
      ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (β := fun _ : r => ℝ) a‖ *
        (‖matrixContinuousLinearMap G‖ * ‖x‖) := by
  have hproj :=
    (PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (β := fun _ : r => ℝ) a).le_opNorm
      (matrixContinuousLinearMap G x)
  have hlin := (matrixContinuousLinearMap G).le_opNorm x
  have hproj_nonneg :
      0 ≤ ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : r => ℝ) a‖ :=
    norm_nonneg _
  calc
    |(((matrixContinuousLinearMap G x : EuclideanSpace ℝ r) : r → ℝ) a)| ≤
        ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
          (β := fun _ : r => ℝ) a‖ *
          ‖matrixContinuousLinearMap G x‖ := by
          simpa [Real.norm_eq_abs] using hproj
    _ ≤ ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
          (β := fun _ : r => ℝ) a‖ *
          (‖matrixContinuousLinearMap G‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left hlin hproj_nonneg

/-- A norm fourth moment of the underlying statistic dominates every
coordinate squared tail of its matrix-linear image.

This is the finite-dimensional moment bridge used in the exact-linearization
face of Hansen Theorem 10.10: the deterministic operator/projection norm
constant is kept explicit. -/
private theorem integral_tail_sq_matrixContinuousLinearMap_coord_le_norm_fourth
    {α d r : Type*} [MeasurableSpace α]
    [Fintype d] [Fintype r] [DecidableEq d]
    {P : Measure α} {T : α → EuclideanSpace ℝ d}
    (G : Matrix r d ℝ) (a : r) {R : ℝ} (hR : 0 < R)
    (hT4 : Integrable (fun x => ‖T x‖ ^ 4) P) :
    (∫ x,
      Set.indicator
        {x | R ≤ |(((matrixContinuousLinearMap G (T x) :
          EuclideanSpace ℝ r) : r → ℝ) a)|}
        (fun x =>
          (((matrixContinuousLinearMap G (T x) :
            EuclideanSpace ℝ r) : r → ℝ) a) ^ 2) x ∂P) ≤
      R⁻¹ ^ 2 *
        ((‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
          (β := fun _ : r => ℝ) a‖ * ‖matrixContinuousLinearMap G‖) ^ 4 *
          ∫ x, ‖T x‖ ^ 4 ∂P) := by
  let C : ℝ :=
    ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (β := fun _ : r => ℝ) a‖ * ‖matrixContinuousLinearMap G‖
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hright_int :
      Integrable (fun x => (R ^ 2)⁻¹ * (C ^ 4 * ‖T x‖ ^ 4)) P := by
    exact (hT4.const_mul ((R ^ 2)⁻¹ * C ^ 4)).congr
      (ae_of_all P fun x => by ring)
  have hleft_nonneg :
      0 ≤ᶠ[ae P]
        fun x =>
          Set.indicator
            {x | R ≤ |(((matrixContinuousLinearMap G (T x) :
              EuclideanSpace ℝ r) : r → ℝ) a)|}
            (fun x =>
              (((matrixContinuousLinearMap G (T x) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 2) x := by
    exact ae_of_all P fun x =>
      Set.indicator_nonneg
        (fun x _ =>
          sq_nonneg
            (((matrixContinuousLinearMap G (T x) :
              EuclideanSpace ℝ r) : r → ℝ) a)) x
  have hpoint :
      (fun x =>
          Set.indicator
            {x | R ≤ |(((matrixContinuousLinearMap G (T x) :
              EuclideanSpace ℝ r) : r → ℝ) a)|}
            (fun x =>
              (((matrixContinuousLinearMap G (T x) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 2) x) ≤ᶠ[ae P]
        fun x => (R ^ 2)⁻¹ * (C ^ 4 * ‖T x‖ ^ 4) := by
    refine ae_of_all P fun x => ?_
    let y : ℝ :=
      (((matrixContinuousLinearMap G (T x) :
        EuclideanSpace ℝ r) : r → ℝ) a)
    have hy_abs_le : |y| ≤ C * ‖T x‖ := by
      simpa [C, y, mul_assoc] using
        abs_matrixContinuousLinearMap_coord_le_opNorm_mul_norm G a (T x)
    have hCnorm_nonneg : 0 ≤ C * ‖T x‖ :=
      mul_nonneg hC_nonneg (norm_nonneg _)
    have hy4_le : y ^ 4 ≤ C ^ 4 * ‖T x‖ ^ 4 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg y) hy_abs_le 4
      have hy4_nonneg : 0 ≤ y ^ 4 := by
        nlinarith [sq_nonneg (y ^ 2)]
      have habs4 : |y| ^ 4 = y ^ 4 := by
        rw [← abs_of_nonneg hy4_nonneg, abs_pow]
      calc
        y ^ 4 = |y| ^ 4 := habs4.symm
        _ ≤ (C * ‖T x‖) ^ 4 := hpow
        _ = C ^ 4 * ‖T x‖ ^ 4 := by ring
    by_cases hx : R ≤ |y|
    · have hR_sq_le : R ^ 2 ≤ y ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ hR.le hx 2
      have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
      have hmul :
          R ^ 2 * y ^ 2 ≤ y ^ 2 * y ^ 2 :=
        mul_le_mul_of_nonneg_right hR_sq_le hy_sq_nonneg
      have hscale_nonneg : 0 ≤ (R ^ 2)⁻¹ :=
        inv_nonneg.mpr (sq_nonneg R)
      have hscaled :
          (R ^ 2)⁻¹ * (R ^ 2 * y ^ 2) ≤
            (R ^ 2)⁻¹ * (y ^ 2 * y ^ 2) :=
        mul_le_mul_of_nonneg_left hmul hscale_nonneg
      have hy_sq_le : y ^ 2 ≤ (R ^ 2)⁻¹ * y ^ 4 := by
        calc
          y ^ 2 = (R ^ 2)⁻¹ * (R ^ 2 * y ^ 2) := by
            field_simp [hR.ne']
          _ ≤ (R ^ 2)⁻¹ * (y ^ 2 * y ^ 2) := hscaled
          _ = (R ^ 2)⁻¹ * y ^ 4 := by ring
      have hscaled_fourth :
          (R ^ 2)⁻¹ * y ^ 4 ≤
            (R ^ 2)⁻¹ * (C ^ 4 * ‖T x‖ ^ 4) :=
        mul_le_mul_of_nonneg_left hy4_le hscale_nonneg
      have hxmem :
          x ∈ {x | R ≤ |(((matrixContinuousLinearMap G (T x) :
            EuclideanSpace ℝ r) : r → ℝ) a)|} := by
        simpa [y] using hx
      change
        Set.indicator
          {x | R ≤ |((matrixContinuousLinearMap G) (T x)).ofLp a|}
          (fun x => ((matrixContinuousLinearMap G) (T x)).ofLp a ^ 2) x ≤
            (R ^ 2)⁻¹ * (C ^ 4 * ‖T x‖ ^ 4)
      rw [Set.indicator_of_mem hxmem]
      simpa [y] using hy_sq_le.trans hscaled_fourth
    · have hxnot :
          x ∉ {x | R ≤ |(((matrixContinuousLinearMap G (T x) :
            EuclideanSpace ℝ r) : r → ℝ) a)|} := by
        simpa [y] using hx
      have hC4_nonneg : 0 ≤ C ^ 4 := by
        nlinarith [sq_nonneg (C ^ 2)]
      have hnorm4_nonneg : 0 ≤ ‖T x‖ ^ 4 := by
        nlinarith [sq_nonneg (‖T x‖ ^ 2)]
      have hright_nonneg :
          0 ≤ (R ^ 2)⁻¹ * (C ^ 4 * ‖T x‖ ^ 4) :=
        mul_nonneg (inv_nonneg.mpr (sq_nonneg R))
          (mul_nonneg hC4_nonneg hnorm4_nonneg)
      change
        Set.indicator
          {x | R ≤ |((matrixContinuousLinearMap G) (T x)).ofLp a|}
          (fun x => ((matrixContinuousLinearMap G) (T x)).ofLp a ^ 2) x ≤
            (R ^ 2)⁻¹ * (C ^ 4 * ‖T x‖ ^ 4)
      rw [Set.indicator_of_notMem hxnot]
      exact hright_nonneg
  calc
    (∫ x,
      Set.indicator
        {x | R ≤ |(((matrixContinuousLinearMap G (T x) :
          EuclideanSpace ℝ r) : r → ℝ) a)|}
        (fun x =>
          (((matrixContinuousLinearMap G (T x) :
            EuclideanSpace ℝ r) : r → ℝ) a) ^ 2) x ∂P) ≤
        ∫ x, (R ^ 2)⁻¹ * (C ^ 4 * ‖T x‖ ^ 4) ∂P :=
      integral_mono_of_nonneg hleft_nonneg hright_int hpoint
    _ = R⁻¹ ^ 2 *
        (C ^ 4 * ∫ x, ‖T x‖ ^ 4 ∂P) := by
      have hfun :
          (fun x => (R ^ 2)⁻¹ * (C ^ 4 * ‖T x‖ ^ 4)) =
            fun x => ((R ^ 2)⁻¹ * C ^ 4) * ‖T x‖ ^ 4 := by
        funext x
        ring
      rw [hfun, integral_const_mul]
      ring

theorem bootstrapUniformSquareTail_of_linearization_coord_normFourth
    [IsFiniteMeasure ν]
    {d q : Type*} [Fintype d] [Fintype q] [DecidableEq d]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    {B : ℝ} (H : Matrix q d ℝ) (a : q)
    (hB : 0 ≤ B)
    (hZlim : MemLp Z 2 ν)
    (hlinearization :
      ∀ n ω ωs, Zstar n ω ωs =
        (((matrixContinuousLinearMap H (Tstar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ) a))
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    BootstrapUniformSquareTail μ Pstar Zstar ν Z := by
  let C : ℝ :=
    ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (β := fun _ : q => ℝ) a‖ * ‖matrixContinuousLinearMap H‖
  have hC4_nonneg : 0 ≤ C ^ 4 := by
    nlinarith [sq_nonneg (C ^ 2)]
  have hCB_nonneg : 0 ≤ C ^ 4 * B :=
    mul_nonneg hC4_nonneg hB
  have hC4 :
      TendstoInMeasure μ (fun _ (_ : Ω) => C ^ 4) atTop
        (fun _ => C ^ 4) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  have hMoment :
      TendstoInMeasure μ
        (fun n ω => C ^ 4 *
          ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => C ^ 4 * B) :=
    TendstoInMeasure.mul_limits_real hC4 hNormFourth
  exact
    bootstrapUniformSquareTail_of_tail_sq_le_tendstoInMeasure_of_memLp_limit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (M := fun n ω => C ^ 4 *
        ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
      (B := C ^ 4 * B) hCB_nonneg hZlim hMoment
      (fun n ω R hR => by
        have hbound :=
          integral_tail_sq_matrixContinuousLinearMap_coord_le_norm_fourth
            (P := Pstar n ω) (T := Tstar n ω) H a
            (zero_lt_one.trans_le hR) (hNormFourthInt n ω)
        have hfun :
            (fun ωs =>
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs) =
              fun ωs =>
                Set.indicator
                  {ωs | R ≤
                    |(((matrixContinuousLinearMap H (Tstar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ) a)|}
                  (fun ωs =>
                    (((matrixContinuousLinearMap H (Tstar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ) a) ^ 2) ωs := by
          funext ωs
          have hz :
              Zstar n ω ωs = (H *ᵥ (Tstar n ω ωs).ofLp) a := by
            simpa [matrixContinuousLinearMap_apply] using
              hlinearization n ω ωs
          by_cases hx : R ≤ |Zstar n ω ωs|
          · have hx' : R ≤ |(H *ᵥ (Tstar n ω ωs).ofLp) a| := by
              simpa [hz] using hx
            simp [Set.indicator, hx', hz, matrixContinuousLinearMap_apply]
          · have hx' : ¬ R ≤ |(H *ᵥ (Tstar n ω ωs).ofLp) a| := by
              simpa [hz] using hx
            simp [Set.indicator, hx', hz, matrixContinuousLinearMap_apply]
        simpa [hfun, C] using hbound)

theorem bootstrapUniformSquareTailIndexed_of_linearization_coord_normFourth
    [IsFiniteMeasure ν]
    {d q : Type*} [Fintype d] [Fintype q] [DecidableEq d]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    {B : ℝ} (H : Matrix q d ℝ) (a : q)
    (hB : 0 ≤ B)
    (hZlim : MemLp Z 2 ν)
    (hlinearization :
      ∀ n ω ωs, Zstar n ω ωs =
        (((matrixContinuousLinearMap H (Tstar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ) a))
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z := by
  let C : ℝ :=
    ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (β := fun _ : q => ℝ) a‖ * ‖matrixContinuousLinearMap H‖
  have hC4_nonneg : 0 ≤ C ^ 4 := by
    nlinarith [sq_nonneg (C ^ 2)]
  have hCB_nonneg : 0 ≤ C ^ 4 * B :=
    mul_nonneg hC4_nonneg hB
  have hC4 :
      TendstoInMeasure μ (fun _ (_ : Ω) => C ^ 4) atTop
        (fun _ => C ^ 4) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  have hMoment :
      TendstoInMeasure μ
        (fun n ω => C ^ 4 *
          ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => C ^ 4 * B) :=
    TendstoInMeasure.mul_limits_real hC4 hNormFourth
  exact
    bootstrapUniformSquareTailIndexed_of_tail_sq_le_tendstoInMeasure_of_memLp_limit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (M := fun n ω => C ^ 4 *
        ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
      (B := C ^ 4 * B) hCB_nonneg hZlim hMoment
      (fun n ω R hR => by
        have hbound :=
          integral_tail_sq_matrixContinuousLinearMap_coord_le_norm_fourth
            (P := Pstar n ω) (T := Tstar n ω) H a
            (zero_lt_one.trans_le hR) (hNormFourthInt n ω)
        have hfun :
            (fun ωs =>
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs) =
              fun ωs =>
                Set.indicator
                  {ωs | R ≤
                    |(((matrixContinuousLinearMap H (Tstar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ) a)|}
                  (fun ωs =>
                    (((matrixContinuousLinearMap H (Tstar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ) a) ^ 2) ωs := by
          funext ωs
          have hz :
              Zstar n ω ωs = (H *ᵥ (Tstar n ω ωs).ofLp) a := by
            simpa [matrixContinuousLinearMap_apply] using
              hlinearization n ω ωs
          by_cases hx : R ≤ |Zstar n ω ωs|
          · have hx' : R ≤ |(H *ᵥ (Tstar n ω ωs).ofLp) a| := by
              simpa [hz] using hx
            simp [Set.indicator, hx', hz, matrixContinuousLinearMap_apply]
          · have hx' : ¬ R ≤ |(H *ᵥ (Tstar n ω ωs).ofLp) a| := by
              simpa [hz] using hx
            simp [Set.indicator, hx', hz, matrixContinuousLinearMap_apply]
        simpa [hfun, C] using hbound)

theorem bootstrapUniformSquareTail_of_normFourth_coord
    [IsFiniteMeasure ν]
    {r : Type*} [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {Z : Ωlim → EuclideanSpace ℝ r}
    {B : ℝ} (a : r)
    (hB : 0 ≤ B)
    (hZlim :
      MemLp (fun z : Ωlim => (Z z : r → ℝ) a) 2 ν)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Zstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    BootstrapUniformSquareTail μ Pstar
      (fun n ω ωs => (Zstar n ω ωs : r → ℝ) a) ν
      (fun z => (Z z : r → ℝ) a) := by
  classical
  exact
    bootstrapUniformSquareTail_of_linearization_coord_normFourth
      (μ := μ) (ν := ν) (Pstar := Pstar) (Tstar := Zstar)
      (Zstar := fun n ω ωs => (Zstar n ω ωs : r → ℝ) a)
      (Z := fun z => (Z z : r → ℝ) a)
      (B := B) (1 : Matrix r r ℝ) a hB hZlim
      (fun n ω ωs => by
        change (Zstar n ω ωs : r → ℝ) a =
          (((matrixContinuousLinearMap (1 : Matrix r r ℝ)
            (Zstar n ω ωs) : EuclideanSpace ℝ r) : r → ℝ) a)
        simp [matrixContinuousLinearMap_apply])
      hNormFourth hNormFourthInt

theorem bootstrapUniformSquareTailIndexed_of_normFourth_coord
    [IsFiniteMeasure ν]
    {r : Type*} [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {Z : Ωlim → EuclideanSpace ℝ r}
    {B : ℝ} (a : r)
    (hB : 0 ≤ B)
    (hZlim :
      MemLp (fun z : Ωlim => (Z z : r → ℝ) a) 2 ν)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Zstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    BootstrapUniformSquareTailIndexed μ Pstar
      (fun n ω ωs => (Zstar n ω ωs : r → ℝ) a) ν
      (fun z => (Z z : r → ℝ) a) := by
  classical
  exact
    bootstrapUniformSquareTailIndexed_of_linearization_coord_normFourth
      (μ := μ) (ν := ν) (Pstar := Pstar) (Tstar := Zstar)
      (Zstar := fun n ω ωs => (Zstar n ω ωs : r → ℝ) a)
      (Z := fun z => (Z z : r → ℝ) a)
      (B := B) (1 : Matrix r r ℝ) a hB hZlim
      (fun n ω ωs => by
        change (Zstar n ω ωs : r → ℝ) a =
          (((matrixContinuousLinearMap (1 : Matrix r r ℝ)
            (Zstar n ω ωs) : EuclideanSpace ℝ r) : r → ℝ) a)
        simp [matrixContinuousLinearMap_apply])
      hNormFourth hNormFourthInt

theorem bootstrapUniformSquareTail_of_normFourth_coord_add
    [IsFiniteMeasure ν]
    {r : Type*} [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {Z : Ωlim → EuclideanSpace ℝ r}
    {B : ℝ} (a c : r)
    (hB : 0 ≤ B)
    (hZlim :
      MemLp (fun z : Ωlim =>
        (Z z : r → ℝ) a + (Z z : r → ℝ) c) 2 ν)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Zstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    BootstrapUniformSquareTail μ Pstar
      (fun n ω ωs =>
        (Zstar n ω ωs : r → ℝ) a + (Zstar n ω ωs : r → ℝ) c)
      ν
      (fun z => (Z z : r → ℝ) a + (Z z : r → ℝ) c) := by
  classical
  let H : Matrix Unit r ℝ :=
    fun _ j => (1 : Matrix r r ℝ) a j + (1 : Matrix r r ℝ) c j
  exact
    bootstrapUniformSquareTail_of_linearization_coord_normFourth
      (μ := μ) (ν := ν) (Pstar := Pstar) (Tstar := Zstar)
      (Zstar := fun n ω ωs =>
        (Zstar n ω ωs : r → ℝ) a + (Zstar n ω ωs : r → ℝ) c)
      (Z := fun z => (Z z : r → ℝ) a + (Z z : r → ℝ) c)
      (B := B) H () hB hZlim
      (fun n ω ωs => by
        have ha :
            (Zstar n ω ωs : r → ℝ) a =
              ((1 : Matrix r r ℝ) *ᵥ (Zstar n ω ωs).ofLp) a := by
          simp
        have hc :
            (Zstar n ω ωs : r → ℝ) c =
              ((1 : Matrix r r ℝ) *ᵥ (Zstar n ω ωs).ofLp) c := by
          simp
        change (Zstar n ω ωs : r → ℝ) a +
            (Zstar n ω ωs : r → ℝ) c =
          (((matrixContinuousLinearMap H (Zstar n ω ωs) :
            EuclideanSpace ℝ Unit) : Unit → ℝ) ())
        rw [ha, hc]
        simp [H, matrixContinuousLinearMap_apply, Matrix.mulVec, dotProduct,
          Finset.sum_add_distrib, add_mul])
      hNormFourth hNormFourthInt

theorem bootstrapUniformSquareTailIndexed_of_normFourth_coord_add
    [IsFiniteMeasure ν]
    {r : Type*} [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {Z : Ωlim → EuclideanSpace ℝ r}
    {B : ℝ} (a c : r)
    (hB : 0 ≤ B)
    (hZlim :
      MemLp (fun z : Ωlim =>
        (Z z : r → ℝ) a + (Z z : r → ℝ) c) 2 ν)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Zstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    BootstrapUniformSquareTailIndexed μ Pstar
      (fun n ω ωs =>
        (Zstar n ω ωs : r → ℝ) a + (Zstar n ω ωs : r → ℝ) c)
      ν
      (fun z => (Z z : r → ℝ) a + (Z z : r → ℝ) c) := by
  classical
  let H : Matrix Unit r ℝ :=
    fun _ j => (1 : Matrix r r ℝ) a j + (1 : Matrix r r ℝ) c j
  exact
    bootstrapUniformSquareTailIndexed_of_linearization_coord_normFourth
      (μ := μ) (ν := ν) (Pstar := Pstar) (Tstar := Zstar)
      (Zstar := fun n ω ωs =>
        (Zstar n ω ωs : r → ℝ) a + (Zstar n ω ωs : r → ℝ) c)
      (Z := fun z => (Z z : r → ℝ) a + (Z z : r → ℝ) c)
      (B := B) H () hB hZlim
      (fun n ω ωs => by
        have ha :
            (Zstar n ω ωs : r → ℝ) a =
              ((1 : Matrix r r ℝ) *ᵥ (Zstar n ω ωs).ofLp) a := by
          simp
        have hc :
            (Zstar n ω ωs : r → ℝ) c =
              ((1 : Matrix r r ℝ) *ᵥ (Zstar n ω ωs).ofLp) c := by
          simp
        change (Zstar n ω ωs : r → ℝ) a +
            (Zstar n ω ωs : r → ℝ) c =
          (((matrixContinuousLinearMap H (Zstar n ω ωs) :
            EuclideanSpace ℝ Unit) : Unit → ℝ) ())
        rw [ha, hc]
        simp [H, matrixContinuousLinearMap_apply, Matrix.mulVec, dotProduct,
          Finset.sum_add_distrib, add_mul])
      hNormFourth hNormFourthInt

theorem isCompact_abs_coord_bound
    {r : Type*}
    {K : Set (EuclideanSpace ℝ r)} (hK : IsCompact K) (a : r) :
    ∃ C : ℝ, ∀ x ∈ K, |((x : EuclideanSpace ℝ r) : r → ℝ) a| ≤ C := by
  have hcont :
      Continuous (fun x : EuclideanSpace ℝ r => ((x : r → ℝ) a)) :=
    (continuous_apply a).comp (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

theorem isCompact_abs_coord_add_bound
    {r : Type*}
    {K : Set (EuclideanSpace ℝ r)} (hK : IsCompact K) (a c : r) :
    ∃ C : ℝ, ∀ x ∈ K,
      |((x : EuclideanSpace ℝ r) : r → ℝ) a +
        ((x : EuclideanSpace ℝ r) : r → ℝ) c| ≤ C := by
  have hcont_a :
      Continuous (fun x : EuclideanSpace ℝ r => ((x : r → ℝ) a)) :=
    (continuous_apply a).comp (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcont_c :
      Continuous (fun x : EuclideanSpace ℝ r => ((x : r → ℝ) c)) :=
    (continuous_apply c).comp (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcont :
      Continuous (fun x : EuclideanSpace ℝ r =>
        ((x : r → ℝ) a) + ((x : r → ℝ) c)) :=
    hcont_a.add hcont_c
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

/-- Hansen Theorem 10.10, smooth-function Gaussian coordinate variance
consistency from the Theorem 10.9 uniform-square-tail premise.

This composes the smooth-function Gaussian bootstrap limit supplied by Hansen
Theorem 10.7 with the scalar Theorem 10.9 variance bridge for a chosen
coordinate. Hansen's bounded-derivative Taylor/Rosenthal argument is the
model-specific route that supplies the uniform-square-tail premise. -/
theorem
    chapter10_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
    {r : Type*} [Fintype r] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {S : Matrix r r ℝ}
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) S)]
    (a : r)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S))
    (hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z))
    (hTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) ^ 2) := by
  have hcoordContinuous :
      Continuous (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    (continuous_apply a).comp (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hweakCoord :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      hGaussian hcoordContinuous
  exact
    chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      hPstar hcoordMem hlimMem hweakCoord hTail

/-- Hansen Theorem 10.10, smooth-function Gaussian coordinate variance
consistency from conditional fourth-moment convergence.

The fourth-moment premise is the formal endpoint of Hansen's
bounded-derivative Taylor/Rosenthal calculation before uniform square
integrability is applied. -/
theorem
    chapter10_smooth_bootstrap_variance_consistency_of_gaussian_fourthMoment
    {r : Type*} [Fintype r] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {S : Matrix r r ℝ}
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) S)]
    {B : ℝ} (a : r)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S))
    (hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z))
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs, ((thetaStar n ω ωs : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω,
        Integrable
          (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) ^ 2) := by
  have hcoordContinuous :
      Continuous (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    (continuous_apply a).comp (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hweakCoord :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      hGaussian hcoordContinuous
  exact
    chapter10_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      hPstar hcoordMem hlimMem hweakCoord hB hFourth hFourthInt

/-- Indexed Hansen Theorem 10.10, smooth-function Gaussian coordinate variance
consistency from the Theorem 10.9 uniform-square-tail premise. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
    {r : Type*} [Fintype r] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {S : Matrix r r ℝ}
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) S)]
    (a : r)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S))
    (hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z))
    (hTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) ^ 2) := by
  have hcoordContinuous :
      Continuous (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    (continuous_apply a).comp (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hweakCoord :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      hGaussian hcoordContinuous
  exact
    chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      hPstar hcoordMem hlimMem hweakCoord hTail

/-- Indexed Hansen Theorem 10.10, smooth-function Gaussian coordinate variance
consistency from conditional fourth-moment convergence. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_gaussian_fourthMoment
    {r : Type*} [Fintype r] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {S : Matrix r r ℝ}
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) S)]
    {B : ℝ} (a : r)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S))
    (hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z))
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs, ((thetaStar n ω ωs : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω,
        Integrable
          (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) ^ 2) := by
  have hcoordContinuous :
      Continuous (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    (continuous_apply a).comp (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hweakCoord :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      hGaussian hcoordContinuous
  exact
    chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      hPstar hcoordMem hlimMem hweakCoord hB hFourth hFourthInt

/-- Hansen Theorem 10.10 smooth-function variance consistency from a
noncompact compact-tail remainder linearization and a named uniform-square-tail
premise.

Theorem 10.7 supplies the Gaussian weak limit through the compact-tail
pointwise remainder route; Theorem 10.9 supplies variance consistency from the
coordinate uniform-square-tail condition. -/
theorem
    chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_uniformSquareTail
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hSqTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
      hthetaStar hCompactTail hR_tail hR_bound
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hSqTail

/-- Hansen Theorem 10.10 smooth-function variance consistency from a
noncompact compact-tail remainder linearization and an eventual deterministic
coordinate bound.

The pointwise bound discharges the scalar uniform-square-tail premise in
`chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_uniformSquareTail`. -/
theorem
    chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_uniformSquareTail
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G a hV hPstar hT
    hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
    (bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      (C := C) hlimMem hbound)

/-- Hansen Theorem 10.10 smooth-function variance consistency from a
noncompact compact-tail remainder linearization and conditional fourth-moment
convergence. -/
theorem
    chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs, ((thetaStar n ω ωs : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω,
        Integrable
          (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
      hthetaStar hCompactTail hR_tail hR_bound
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_gaussian_fourthMoment
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hB
      hFourth hFourthInt

/-- Hansen Theorem 10.10 smooth-function variance consistency from a
noncompact compact-tail remainder linearization and a norm fourth-moment
premise on the nonlinear smooth statistic.

The norm fourth moment of `thetaStar` supplies the coordinate
uniform-square-tail condition used by the scalar compact-tail remainder
variance wrapper. -/
theorem
    chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hSqTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    bootstrapUniformSquareTail_of_normFourth_coord
      (μ := μ)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Pstar := Pstar) (Zstar := thetaStar)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (B := B) a hB hlimMem hNormFourth hNormFourthInt
  exact
    chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G a hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hSqTail

/-- Hansen Theorem 10.10 smooth-function variance consistency from a
quadratic Taylor-remainder envelope and norm fourth-moment premises.

The envelope `dist θ* (G T*) ≤ ρₙ ‖T*‖²`, together with `ρₙ² → 0` and a
conditional fourth-moment convergence premise on `T*`, supplies the compact-tail
remainder-tail condition. The separate norm fourth-moment premise on `thetaStar`
supplies the coordinate uniform-square-tail condition for the variance. -/
theorem
    chapter10_smooth_bootstrap_variance_of_quadratic_remainder_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bθ BT : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_normFourthMoment
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G a hV hPstar hT hTstar hthetaStar hcoordMem hlimMem
    hCompactTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hBθ hThetaNormFourth hThetaNormFourthInt

/-- Indexed Hansen Theorem 10.10 smooth-function variance consistency from a
noncompact compact-tail remainder linearization and a named
uniform-square-tail premise. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_uniformSquareTail
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hSqTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
      hthetaStar hCompactTail hR_tail hR_bound
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hSqTail

/-- Indexed Hansen Theorem 10.10 smooth-function variance consistency from a
noncompact compact-tail remainder linearization and an eventual deterministic
coordinate bound. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_uniformSquareTail
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G a hV hPstar hT
    hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
    (bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      (C := C) hlimMem hbound)

/-- Indexed Hansen Theorem 10.10 smooth-function variance consistency from a
noncompact compact-tail remainder linearization and conditional fourth-moment
convergence. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs, ((thetaStar n ω ωs : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω,
        Integrable
          (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
      hthetaStar hCompactTail hR_tail hR_bound
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_gaussian_fourthMoment
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hB
      hFourth hFourthInt

/-- Indexed Hansen Theorem 10.10 smooth-function variance consistency from a
noncompact compact-tail remainder linearization and an indexed norm
fourth-moment premise on the nonlinear smooth statistic. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hSqTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    bootstrapUniformSquareTailIndexed_of_normFourth_coord
      (μ := μ)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Pstar := Pstar) (Zstar := thetaStar)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (B := B) a hB hlimMem hNormFourth hNormFourthInt
  exact
    chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G a hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hSqTail

/-- Indexed Hansen Theorem 10.10 smooth-function variance consistency from a
quadratic Taylor-remainder envelope and indexed norm fourth-moment premises. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_of_quadratic_remainder_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bθ BT : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_normFourthMoment
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G a hV hPstar hT hTstar hthetaStar hcoordMem hlimMem
    hCompactTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hBθ hThetaNormFourth hThetaNormFourthInt

/-- Hansen Theorem 10.10 smooth-function variance consistency from a
compact-range quadratic Taylor-remainder envelope and norm fourth-moment
premises.

The fixed compact range removes the noncompact compact-tail premise, while the
quadratic envelope and fourth moment of the linearized statistic discharge the
remainder-tail premise. The separate norm fourth-moment premise on
`thetaStar` supplies the coordinate uniform-square-tail condition for the
variance. -/
theorem
    chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_smooth_gaussian_of_compact_range_quadratic_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (BT := BT) (V := V) G
      hV hT hK hPstar hTstar hthetaStar hlinearized_mem hthetaStar_mem
      hρsq hTNormFourth hTNormFourthInt hR_bound
  have hSqTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    bootstrapUniformSquareTail_of_normFourth_coord
      (μ := μ)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Pstar := Pstar) (Zstar := thetaStar)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (B := Bθ) a hBθ hlimMem hThetaNormFourth hThetaNormFourthInt
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hSqTail

/-- Indexed Hansen Theorem 10.10 smooth-function variance consistency from a
compact-range quadratic Taylor-remainder envelope and indexed norm
fourth-moment premises. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_smooth_gaussian_of_compact_range_quadratic_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (BT := BT) (V := V) G
      hV hT hK hPstar hTstar hthetaStar hlinearized_mem hthetaStar_mem
      hρsq hTNormFourth hTNormFourthInt hR_bound
  have hSqTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    bootstrapUniformSquareTailIndexed_of_normFourth_coord
      (μ := μ)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Pstar := Pstar) (Zstar := thetaStar)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (B := Bθ) a hBθ hlimMem hThetaNormFourth hThetaNormFourthInt
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hSqTail

/-- Hansen Theorem 10.10 smooth-function variance consistency from a
compact-range quadratic Taylor-remainder envelope.

The fixed compact range gives the deterministic coordinate bound needed for
Hansen's uniform-square-tail condition, so this wrapper does not require a
separate nonlinear norm-fourth premise on `thetaStar`. -/
theorem
    chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {BT : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  obtain ⟨C, hC⟩ := isCompact_abs_coord_bound hK a
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_smooth_gaussian_of_compact_range_quadratic_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (BT := BT) (V := V) G
      hV hT hK hPstar hTstar hthetaStar hlinearized_mem hthetaStar_mem
      hρsq hTNormFourth hTNormFourthInt hR_bound
  have hTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      (C := C) hlimMem
      (Eventually.of_forall fun n ω ωs => hC _ (hthetaStar_mem n ω ωs))
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hTail

/-- Indexed counterpart of
`chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_eventualBound`. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_of_compact_range_quadratic_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {BT : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  obtain ⟨C, hC⟩ := isCompact_abs_coord_bound hK a
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_smooth_gaussian_of_compact_range_quadratic_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (BT := BT) (V := V) G
      hV hT hK hPstar hTstar hthetaStar hlinearized_mem hthetaStar_mem
      hρsq hTNormFourth hTNormFourthInt hR_bound
  have hTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      (C := C) hlimMem
      (Eventually.of_forall fun n ω ωs => hC _ (hthetaStar_mem n ω ωs))
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hTail

/-- Hansen Theorem 10.10, smooth-function variance consistency from exact
derivative linearization and the Theorem 10.9 uniform-square-tail premise.

The exact linearization supplies the smooth Gaussian weak limit from Hansen
Theorem 10.7. The scalar coordinate tail premise is still stated on the smooth
statistic itself, so the model-specific Taylor/Rosenthal step remains explicit. -/
theorem
    chapter10_smooth_bootstrap_variance_consistency_of_linearization_uniformSquareTail
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_smooth_function_gaussian_of_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hTail

/-- Indexed Hansen Theorem 10.10, smooth-function variance consistency from
exact derivative linearization and the indexed Theorem 10.9
uniform-square-tail premise. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_uniformSquareTail
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_gaussian_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hTail

/-- Hansen Theorem 10.10, smooth-function variance consistency from exact
derivative linearization and an eventual deterministic coordinate bound.

The coordinate bound discharges Hansen's uniform-square-tail condition through
the bounded-statistic Theorem 10.9 constructor before the smooth Gaussian
linearization route is applied. -/
theorem
    chapter10_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_smooth_bootstrap_variance_consistency_of_linearization_uniformSquareTail
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem hlimMem
    hlinearization
    (bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      (C := C) hlimMem hbound)

/-- Indexed Hansen Theorem 10.10, smooth-function variance consistency from
exact derivative linearization and an eventual deterministic coordinate bound. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_uniformSquareTail
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem hlimMem
    hlinearization
    (bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      (C := C) hlimMem hbound)

/-- Hansen Theorem 10.10, smooth-function variance consistency from exact
derivative linearization and a linearized fourth-moment premise.

This is the exact-linearization face of the bounded-derivative calculation:
the smooth statistic is first reduced to `G T*` using Hansen Theorem 10.7's
linearization route, then the scalar fourth-moment premise is rewritten through
that equality and fed to the Gaussian fourth-moment variance wrapper above. -/
theorem
    chapter10_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hFourthLinear :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthLinearInt :
      ∀ n ω,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_smooth_function_gaussian_of_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hFourthTheta :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs, ((thetaStar n ω ωs : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hFourthLinear
    refine ae_of_all μ fun ω => ?_
    have hfun :
        (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4) =
          fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simp [hfun]
  have hFourthThetaInt :
      ∀ n ω,
        Integrable
          (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4)
          (Pstar n ω) := by
    intro n ω
    have hfun :
        (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4) =
          fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simpa [hfun] using hFourthLinearInt n ω
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_gaussian_fourthMoment
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hB
      hFourthTheta hFourthThetaInt

/-- Indexed Hansen Theorem 10.10, smooth-function variance consistency from
exact derivative linearization and a linearized fourth-moment premise. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hFourthLinear :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthLinearInt :
      ∀ n ω,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hFourthTheta :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs, ((thetaStar n ω ωs : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hFourthLinear
    refine ae_of_all μ fun ω => ?_
    have hfun :
        (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4) =
          fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simp [hfun]
  have hFourthThetaInt :
      ∀ n ω,
        Integrable
          (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4)
          (Pstar n ω) := by
    intro n ω
    have hfun :
        (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4) =
          fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simpa [hfun] using hFourthLinearInt n ω
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_gaussian_fourthMoment
      (μ := μ) (Pstar := Pstar) (thetaStar := thetaStar)
      (S := G * V * Gᵀ) a hPstar hcoordMem hlimMem hGaussian hB
      hFourthTheta hFourthThetaInt

/-- Hansen Theorem 10.10, smooth-function variance consistency from exact
derivative linearization and a norm fourth-moment premise on the underlying
bootstrap statistic.

The norm fourth moment of `T*` dominates each coordinate squared tail of
`G T*`; exact linearization transfers that tail control to the smooth statistic
coordinate. This removes the coordinate-specific fourth-moment premise while
leaving the genuinely nonlinear Taylor remainder step explicit. -/
theorem
    chapter10_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  let C : ℝ :=
    ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (β := fun _ : r => ℝ) a‖ * ‖matrixContinuousLinearMap G‖
  have hC4_nonneg : 0 ≤ C ^ 4 := by
    nlinarith [sq_nonneg (C ^ 2)]
  have hCB_nonneg : 0 ≤ C ^ 4 * B :=
    mul_nonneg hC4_nonneg hB
  have hC4 :
      TendstoInMeasure μ (fun _ (_ : Ω) => C ^ 4) atTop
        (fun _ => C ^ 4) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  have hMoment :
      TendstoInMeasure μ
        (fun n ω => C ^ 4 *
          ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => C ^ 4 * B) :=
    TendstoInMeasure.mul_limits_real hC4 hNormFourth
  have hTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    bootstrapUniformSquareTail_of_tail_sq_le_tendstoInMeasure_of_memLp_limit
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      (M := fun n ω => C ^ 4 *
        ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
      (B := C ^ 4 * B) hCB_nonneg hlimMem hMoment
      (fun n ω R hR => by
        have hbound :=
          integral_tail_sq_matrixContinuousLinearMap_coord_le_norm_fourth
            (P := Pstar n ω) (T := Tstar n ω) G a
            (zero_lt_one.trans_le hR) (hNormFourthInt n ω)
        have hfun :
            (fun ωs =>
              Set.indicator
                {ωs | R ≤ |((thetaStar n ω ωs : r → ℝ) a)|}
                (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 2) ωs) =
              fun ωs =>
                Set.indicator
                  {ωs | R ≤
                    |(((matrixContinuousLinearMap G (Tstar n ω ωs) :
                      EuclideanSpace ℝ r) : r → ℝ) a)|}
                  (fun ωs =>
                    (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                      EuclideanSpace ℝ r) : r → ℝ) a) ^ 2) ωs := by
          funext ωs
          have hcoord :
              ((thetaStar n ω ωs : r → ℝ) a) =
                (G *ᵥ (Tstar n ω ωs).ofLp) a := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
                (hlinearization n ω ωs)
          simp [Set.indicator, hcoord, matrixContinuousLinearMap_apply]
        simpa [hfun, C] using hbound)
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_linearization_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem hlimMem
      hlinearization hTail

/-- Indexed Hansen Theorem 10.10, smooth-function variance consistency from
exact derivative linearization and an indexed norm fourth-moment premise on
the underlying bootstrap statistic. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  let C : ℝ :=
    ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
      (β := fun _ : r => ℝ) a‖ * ‖matrixContinuousLinearMap G‖
  have hC4_nonneg : 0 ≤ C ^ 4 := by
    nlinarith [sq_nonneg (C ^ 2)]
  have hCB_nonneg : 0 ≤ C ^ 4 * B :=
    mul_nonneg hC4_nonneg hB
  have hC4 :
      TendstoInMeasure μ (fun _ (_ : Ω) => C ^ 4) atTop
        (fun _ => C ^ 4) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  have hMoment :
      TendstoInMeasure μ
        (fun n ω => C ^ 4 *
          ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => C ^ 4 * B) :=
    TendstoInMeasure.mul_limits_real hC4 hNormFourth
  have hTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) :=
    bootstrapUniformSquareTailIndexed_of_tail_sq_le_tendstoInMeasure_of_memLp_limit
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
      (M := fun n ω => C ^ 4 *
        ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
      (B := C ^ 4 * B) hCB_nonneg hlimMem hMoment
      (fun n ω R hR => by
        have hbound :=
          integral_tail_sq_matrixContinuousLinearMap_coord_le_norm_fourth
            (P := Pstar n ω) (T := Tstar n ω) G a
            (zero_lt_one.trans_le hR) (hNormFourthInt n ω)
        have hfun :
            (fun ωs =>
              Set.indicator
                {ωs | R ≤ |((thetaStar n ω ωs : r → ℝ) a)|}
                (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 2) ωs) =
              fun ωs =>
                Set.indicator
                  {ωs | R ≤
                    |(((matrixContinuousLinearMap G (Tstar n ω ωs) :
                      EuclideanSpace ℝ r) : r → ℝ) a)|}
                  (fun ωs =>
                    (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                      EuclideanSpace ℝ r) : r → ℝ) a) ^ 2) ωs := by
          funext ωs
          have hcoord :
              ((thetaStar n ω ωs : r → ℝ) a) =
                (G *ᵥ (Tstar n ω ωs).ofLp) a := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
                (hlinearization n ω ωs)
          simp [Set.indicator, hcoord, matrixContinuousLinearMap_apply]
        simpa [hfun, C] using hbound)
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem hlimMem
      hlinearization hTail

end BootstrapVariance

end HansenEconometrics
