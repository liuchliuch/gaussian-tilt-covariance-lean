import GaussianTilt.MomentMapRegularityBallHessian
import GaussianTilt.MomentMapTransport

/-! # Exact Euclidean-to-coordinate moment-source transport

The canonical coordinate equivalence is volume preserving. Source densities,
probability normalization, strict convexity and actual gradient pushforwards
are transported, without adding a Jacobian or model-identification premise.
-/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff ENNReal

namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateEquiv_measurePreserving : MeasurePreserving (coordinateEquiv n) :=
  PiLp.volume_preserving_ofLp (Fin n)

theorem map_density_coordinateEquiv (f : E n → ℝ) :
    Measure.map (coordinateEquiv n) (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (f ((coordinateEquiv n).symm y))) := by
  let e := coordinateEquiv n
  have h := GaussianTilt.map_withDensity_comp e.toHomeomorph.measurableEmbedding volume
    (fun y ↦ ENNReal.ofReal (f (e.symm y)))
  change Measure.map e (volume.withDensity (fun x ↦ ENNReal.ofReal (f (e.symm (e x))))) =
    (Measure.map e volume).withDensity (fun y ↦ ENNReal.ofReal (f (e.symm y))) at h
  simp only [e.symm_apply_apply] at h
  rw [h]
  congr 1
  exact coordinateEquiv_measurePreserving.map_eq

lemma coordinate_potentialMeasure (φ : E n → ℝ) :
    Measure.map (coordinateEquiv n)
      (volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-φ x)))) =
        potentialMeasure (coordinatePullback φ) := by
  exact map_density_coordinateEquiv (fun x ↦ Real.exp (-φ x))

lemma contDiff_coordinatePullback {φ : E n → ℝ} {m : WithTop ℕ∞}
    (hφ : ContDiff ℝ m φ) : ContDiff ℝ m (coordinatePullback φ) :=
  hφ.comp (coordinateEquiv n).symm.contDiff

lemma strictConvex_coordinatePullback {φ : E n → ℝ} (hφ : StrictConvexOn ℝ univ φ) :
    StrictConvexOn ℝ univ (coordinatePullback φ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have h := hφ.2 (mem_univ ((coordinateEquiv n).symm x)) (mem_univ ((coordinateEquiv n).symm y))
    ((coordinateEquiv n).symm.injective.ne hxy) ha hb hab
  simpa only [coordinatePullback, Function.comp_apply, map_add, map_smul] using h

lemma coordinate_source_probability (φ : E n → ℝ)
    [IsProbabilityMeasure (volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-φ x))))] :
    IsProbabilityMeasure (potentialMeasure (coordinatePullback φ)) := by
  rw [← coordinate_potentialMeasure]
  exact Measure.isProbabilityMeasure_map (coordinateEquiv n).continuous.measurable.aemeasurable

/-- The actual raw-coordinate gradient law is the coordinate image of the
actual Euclidean gradient law; both source and target measures are moved. -/
theorem coordinate_moment_transport {φ : E n → ℝ} (hφ : ContDiff ℝ 1 φ)
    {μ : Measure (E n)}
    (hmap : (volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-φ x)))).map (gradient φ) = μ) :
    momentMeasure (coordinatePullback φ) = μ.map (coordinateEquiv n) := by
  have hraw := contDiff_coordinatePullback hφ
  have hg := (continuous_coordinateGradient hraw).measurable
  have he := (coordinateEquiv n).continuous.measurable
  have hge := MomentMapCoercivity.measurable_actual_gradient φ
  rw [momentMeasure, ← coordinate_potentialMeasure, Measure.map_map hg he,
    ← hmap, Measure.map_map he hge]
  congr 1
  funext x
  simpa only [Function.comp_apply, (coordinateEquiv n).symm_apply_apply] using
    coordinateGradient_pullback (hφ.differentiable le_rfl) ((coordinateEquiv n) x)

end GaussianTilt.MomentMapRegularity
