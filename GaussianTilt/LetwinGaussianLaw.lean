import GaussianTilt.LetwinGaussianPotential
import GaussianTilt.LetwinGaussianCoupling
import GaussianTilt.LogConcaveLinearImages

/-! # Identifying the smoothed moment coupling with a genuine smooth Gibbs law -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped ContDiff ENNReal
namespace GaussianTilt.Letwin
open LogConcaveMarginal

lemma noisyMomentMeasure_eq_perturb {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    noisyMomentMeasure φ T r = ((linearMomentMeasure φ T).prod (coordinateGaussian n)).map
      (fun p => p.1+r•p.2) := by
  have hprod := Measure.map_prod_map (potentialMeasure φ) (coordinateGaussian n)
    (continuous_linearMomentMap hφ T).measurable measurable_id
  simp only [Measure.map_id] at hprod
  rw [linearMomentMeasure, hprod, Measure.map_map (by fun_prop)
    ((continuous_linearMomentMap hφ T).measurable.prodMap measurable_id)]
  rfl

lemma coordinate_exists_compact_density {n : ℕ} {μ : Measure (CoordinateSpace n)}
    {f : CoordinateSpace n → ℝ} (hf : IsLogConcave f) (hfm : Measurable f)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hc : ∃ K : Set (CoordinateSpace n), IsCompact K ∧ μ Kᶜ=0) :
    ∃ (g : CoordinateSpace n → ℝ) (R : ℝ), IsLogConcave g ∧ Measurable g ∧
      (∀ x, R < ‖x‖ → g x=0) ∧ μ=volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
  obtain ⟨K,hK,hzero⟩ := hc
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : CoordinateSpace n)
  let S := Metric.closedBall (0 : CoordinateSpace n) R
  have hSm : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hSae : ∀ᵐ x ∂μ, x∈S := (ae_iff.mpr hzero).mono (fun x hx => hR hx)
  refine ⟨S.indicator f,R,ScalarLogConcaveMoments.logconcave_indicator hf (convex_closedBall _ _),
    hfm.indicator hSm, ?_, ?_⟩
  · intro x hx
    apply indicator_of_notMem
    simpa only [S, Metric.mem_closedBall, dist_zero_right, not_le] using hx
  · rw [show (fun x => ENNReal.ofReal (S.indicator f x)) =
        S.indicator (fun x => ENNReal.ofReal (f x)) by
      funext x; by_cases hx : x∈S <;> simp [hx]]
    rw [withDensity_indicator hSm, ← restrict_withDensity hSm, ← hμ]
    exact (Measure.restrict_eq_self_of_ae_mem hSae).symm

/-- All law-level regularity required by the smooth full-support H⁻¹ theorem
is constructed for every nonzero noise scale. -/
theorem noisyMomentMeasure_has_smooth_convex_potential {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x∈K)
    {f : CoordinateSpace n → ℝ} (hf : IsLogConcave f) (hfm : Measurable f)
    (hμ : momentMeasure φ=volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det≠0) (r : ℝ) (hr : r≠0) :
    ∃ V : CoordinateSpace n → ℝ, ContDiff ℝ ∞ V ∧ ConvexOn ℝ univ V ∧
      noisyMomentMeasure φ T r=potentialMeasure V := by
  letI := linearMomentMeasure_probability hφ T
  obtain ⟨g,hg,hgm,hgμ⟩ := linearMomentMeasure_logconcaveDensity hφ hf hfm hμ T hT
  obtain ⟨g',R,hg',hgm',hgs',hμ'⟩ := coordinate_exists_compact_density hg hgm hgμ
    (linearMomentMeasure_compactSupport hφ hK hgrad T)
  obtain ⟨V,hV,hVc,hVμ⟩ := exists_smooth_convex_potential_coordinateGaussian_convolution hg' hgm' hμ' hgs' r hr
  exact ⟨V,hV,hVc,(noisyMomentMeasure_eq_perturb hφ T r).trans hVμ⟩

end GaussianTilt.Letwin
