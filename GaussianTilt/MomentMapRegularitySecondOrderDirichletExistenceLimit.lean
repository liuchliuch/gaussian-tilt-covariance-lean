import GaussianTilt.MomentMapRegularitySecondOrderDirichletCompactness
import GaussianTilt.MomentMapRegularitySecondOrderDirichletAtomization

/-!
# The complete compact-limit step for Dirichlet construction

Actual weakly convergent finite-measure solutions yield a limiting solution.
Uniform bounds, boundary equicontinuity, Arzelà--Ascoli, convergence of the
supporting images, and retention of the equation are all proved upstream.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Weak convergence of finite right-hand sides and actual Dirichlet
solutions produces a solution for the limiting measure. The subsequence
and all compactness estimates are constructed, not assumed. -/
theorem exists_dirichlet_limit_of_weakly_convergent_solutions [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {v : ℕ → E n → ℝ} (hv : ∀ k, ConvexOn ℝ S (v k))
    (hvc : ∀ k, ContinuousOn (v k) S) (hb : ∀ k, ∀ x ∈ frontier S, v k x = 0)
    {μ : FiniteMeasure (E n)} {ms : ℕ → FiniteMeasure (E n)}
    (hweak : Tendsto ms atTop (𝓝 μ))
    (hmass : ∀ k, (ms k : Measure (E n)) univ = (μ : Measure (E n)) univ)
    (hsol : ∀ k, ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S (v k) A) = (ms k : Measure (E n)) A) :
    ∃ u : E n → ℝ, Continuous u ∧ ConvexOn ℝ S u ∧
      (∀ x ∈ frontier S, u x = 0) ∧
      ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
        volume (subgradientImageOn S u A) = (μ : Measure (E n)) A := by
  let M : ℝ := ((μ : Measure (E n)) univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hmassbound (k : ℕ) : volume (subgradientImageOn S (v k) (interior S)) ≤ ENNReal.ofReal M := by
    rw [alexandrovOn_identity_on_open_of_on_compact hS (hsol k) isOpen_interior Subset.rfl,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact (measure_mono (subset_univ _)).trans_eq (hmass k)
  obtain ⟨j, hj, u, huc, hu, hub, hunif⟩ :=
    exists_continuous_dirichlet_subsequence hS hv hvc hb hM hmassbound
  refine ⟨u, huc, hu, hub, ?_⟩
  exact alexandrovOn_identity_of_uniform_limit_of_weak_convergence hS hSn huc.continuousOn
    (fun k => hvc (j k)) hunif (hweak.comp hj.tendsto_atTop) (fun k => hmass (j k))
    (fun k => hsol (j k))

end GaussianTilt.MomentMapRegularity
