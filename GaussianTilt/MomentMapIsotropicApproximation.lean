import GaussianTilt.MomentMapRegularTargets
import GaussianTilt.WhiteningApproximation
import GaussianTilt.AffineDensityTransportSmooth

/-! # Actual isotropic regular targets in Letwin A1

Gaussian perturbation, normalized ball truncation, and the actual inverse-
covariance affine map construct smooth convex target densities on bounded
open convex sets. A tail reindexing makes every approximant isotropic, and
all polynomial moments through degree four converge.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators ContDiff
namespace GaussianTilt.MomentMapApproximation
open Paouris
variable {n : ℕ}

def RegularIsotropicTarget (μ : Measure (Reference.Space n)) : Prop :=
  IsProbabilityMeasure μ ∧ Reference.compactlySupported μ ∧ Reference.isotropic μ ∧
    Reference.logconcave μ ∧ ∃ D : Set (Reference.Space n), ∃ V : Reference.Space n → ℝ,
      IsOpen D ∧ Convex ℝ D ∧ Bornology.IsBounded D ∧ ContDiff ℝ ∞ V ∧ ConvexOn ℝ univ V ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (D.indicator (fun y => Real.exp (-V y)) x))

theorem eventually_whitened_regular_targets
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hcompact : Reference.compactlySupported μ) (hiso : Reference.isotropic μ)
    (hlog : Reference.logconcave μ) :
    ∀ᶠ k in atTop, RegularIsotropicTarget
      (Whitening.law (perturbedTruncation μ (standardGaussian n) k)) := by
  have hpd := Whitening.eventually_perturbedTruncation_covariance_posDef μ (standardGaussian n)
    (Reference.isotropic_norm_sq_integrable hiso) (standardGaussian_norm_sq_integrable n) hiso
  filter_upwards [hpd] with k hCref
  let ρ := perturbedTruncation μ (standardGaussian n) k
  have hρcomp : Reference.compactlySupported ρ := perturbedTruncation_compactlySupported μ (standardGaussian n) k
  have hX := Whitening.compact_coordinates_memLp hρcomp
  have hC : (Whitening.covariance ρ).PosDef := by
    rw [Whitening.covariance_eq_reference hX]
    exact hCref
  let e := (Whitening.rootEquiv hC).symm
  let m := Whitening.center ρ
  let D := (fun x : Reference.Space n => e (x - m)) '' Metric.ball 0 ((k : ℝ) + 1)
  have hDopen : IsOpen D := by
    dsimp only [D]
    rw [AffineDensityTransport.affine_image_eq_inverse_preimage]
    exact Metric.isOpen_ball.preimage (e.symm.continuous.add continuous_const)
  have hDconv : Convex ℝ D := AffineDensityTransport.convex_affine_image e m (convex_ball 0 _)
  have hDbd : Bornology.IsBounded D := by
    have hc : IsCompact ((fun x : Reference.Space n => e (x - m)) '' Metric.closedBall 0 ((k : ℝ) + 1)) :=
      (isCompact_closedBall _ _).image (e.continuous.comp (continuous_id.sub continuous_const))
    exact hc.isBounded.subset (Set.image_mono Metric.ball_subset_closedBall)
  obtain ⟨V, hVs, hVc, hVlaw⟩ := exists_smooth_convex_potential_perturbedTruncation μ hcompact hlog k
  obtain ⟨W, hWs, hWc, hWlaw⟩ := AffineDensityTransport.exists_smooth_convex_potential_map_affine_indicator
    e m volume volume hVs hVc (convex_ball 0 ((k : ℝ) + 1)) Metric.isOpen_ball.measurableSet
  have hlaw : Whitening.law ρ = volume.withDensity
      (fun x => ENNReal.ofReal (D.indicator (fun y => Real.exp (-W y)) x)) := by
    change Measure.map (fun x => e (x - m)) ρ = _
    rw [show ρ = volume.withDensity (fun x => ENNReal.ofReal
      ((Metric.ball 0 ((k : ℝ) + 1)).indicator (fun y => Real.exp (-V y)) x)) from hVlaw]
    exact hWlaw
  have hLC : Reference.logconcave (Whitening.law ρ) := by
    have hg := ScalarLogConcaveMoments.logconcave_indicator
      (AffineDensityTransport.logconcave_exp_neg_of_convex hWc) hDconv
    exact ⟨D.indicator (fun y => Real.exp (-W y)),
      ⟨hg.1, ((Real.continuous_exp.comp hWs.continuous.neg).measurable.indicator hDopen.measurableSet), hg.2⟩, hlaw⟩
  exact ⟨inferInstance, Whitening.law_compactlySupported hρcomp, Whitening.law_isotropic hX hC,
    hLC, D, W, hDopen, hDconv, hDbd, hWs, hWc, hlaw⟩

lemma compact_norm_fourth_integrable {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hcompact : Reference.compactlySupported μ) : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ := by
  obtain ⟨K, hK, hμK⟩ := hcompact
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_norm.pow 4).continuousOn
  apply Integrable.of_bound (continuous_norm.pow 4).aestronglyMeasurable B
  filter_upwards [show ∀ᵐ x ∂μ, x ∈ K from ae_iff.mpr hμK] with x hx
  exact hB x hx

/-- Letwin A1 for compact input laws: every approximant has the full regular
isotropic density geometry, and every actual degree-at-most-four polynomial
moment converges. Neither the regular sequence nor its moments are inputs. -/
theorem exists_regular_isotropic_approximants
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hcompact : Reference.compactlySupported μ) (hiso : Reference.isotropic μ)
    (hlog : Reference.logconcave μ) :
    ∃ ν : ℕ → Measure (Reference.Space n),
      (∀ k, RegularIsotropicTarget (ν k)) ∧
      ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 4 →
        Tendsto (fun k => ∫ x, MvPolynomial.eval (fun i => x i) p ∂ν k)
          atTop (𝓝 (∫ x, MvPolynomial.eval (fun i => x i) p ∂μ)) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_whitened_regular_targets μ hcompact hiso hlog)
  let ν := fun k => Whitening.law (perturbedTruncation μ (standardGaussian n) (k + N))
  refine ⟨ν, fun k => hN (k + N) (Nat.le_add_left _ _), ?_⟩
  intro p hp
  have ht : Tendsto (fun k : ℕ => k + N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact Filter.eventually_atTop.mpr ⟨b, fun k hk => hk.trans (Nat.le_add_right k N)⟩
  exact (Whitening.gaussianTruncation_whitened_polynomial_moment_tendsto μ
    (compact_norm_fourth_integrable hcompact) hiso p hp).comp ht

end GaussianTilt.MomentMapApproximation
