import GaussianTilt.MomentMapStrongApproximationDensity

/-! # Full regular geometry for the actual whitened strong approximation -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators ContDiff
namespace GaussianTilt.MomentMapApproximation
open Paouris
variable {n : ℕ}

theorem eventually_whitened_strongTruncation_regular_targets
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hcompact : Reference.compactlySupported μ) (hiso : Reference.isotropic μ)
    (hlog : Reference.logconcave μ) :
    ∀ᶠ k in atTop, RegularIsotropicTarget
      (Whitening.law (strongTruncation μ k)) := by
  have hpd := eventually_strongTruncation_covariance_posDef μ
    (compact_norm_fourth_integrable hcompact) hiso
  filter_upwards [hpd] with k hC
  let ρ := strongTruncation μ k
  have hρcomp : Reference.compactlySupported ρ := strongTruncation_compactlySupported μ k
  have hX := Whitening.compact_coordinates_memLp hρcomp
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
  obtain ⟨V, hVs, hVstrong, hVlaw⟩ := exists_strong_potential_strongTruncation μ hcompact hlog k
  have hVc := convexOn_of_strong hVstrong (mul_nonneg (by norm_num) (tiltScale_pos k).le)
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


/-- Genuine strongly regular approximants, with actual centering and inverse-
covariance whitening, converge in every continuous fourth-growth observable. -/
theorem exists_regular_strong_isotropic_approximants
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hcompact : Reference.compactlySupported μ) (hiso : Reference.isotropic μ)
    (hlog : Reference.logconcave μ) :
    ∃ N : ℕ, (∀ k, RegularIsotropicTarget (Whitening.law (strongTruncation μ (k + N)))) ∧
      (∀ k, (Whitening.covariance (strongTruncation μ (k + N))).PosDef) ∧
      ∀ (f : Reference.Space n → ℝ), Continuous f → ∀ C : ℝ, 0 ≤ C →
        (∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ 4)) →
        Tendsto (fun k => ∫ x, f x ∂Whitening.law (strongTruncation μ (k + N)))
          atTop (𝓝 (∫ x, f x ∂μ)) := by
  have he := (eventually_whitened_strongTruncation_regular_targets μ hcompact hiso hlog).and
    (eventually_strongTruncation_covariance_posDef μ (compact_norm_fourth_integrable hcompact) hiso)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  refine ⟨N, fun k => (hN (k + N) (Nat.le_add_left _ _)).1,
    fun k => (hN (k + N) (Nat.le_add_left _ _)).2, ?_⟩
  intro f hf C hC hbound
  have ht : Tendsto (fun k : ℕ => k + N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact Filter.eventually_atTop.mpr ⟨b, fun k hk => hk.trans (Nat.le_add_right k N)⟩
  exact (integral_whitened_strongTruncation_tendsto μ
    (compact_norm_fourth_integrable hcompact) hiso hf hC hbound).comp ht

end GaussianTilt.MomentMapApproximation
