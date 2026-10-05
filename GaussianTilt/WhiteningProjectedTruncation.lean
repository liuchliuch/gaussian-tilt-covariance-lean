import GaussianTilt.WhiteningTruncation
import GaussianTilt.LogConcaveLinearImages
import GaussianTilt.IsotropicIntegrability

/-! # Actual projected pure truncations

Projection follows the original source restriction, rather than truncating
the target law. Integrable target observables pull back through the actual
linear map, proving all target moment and whitening controls.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter Set
open scoped BigOperators Matrix.Norms.L2Operator Topology ENNReal
namespace GaussianTilt.Whitening
variable {n m : ℕ}

/-- Source restriction followed by the given continuous linear projection. -/
def projectedRestriction (μ : Measure (Reference.Space n))
    (L : Reference.Space n →L[ℝ] Reference.Space m) (j : ℕ) : Measure (Reference.Space m) :=
  (ballRestriction μ j).map L

lemma integral_projectedRestriction (μ : Measure (Reference.Space n))
    (L : Reference.Space n →L[ℝ] Reference.Space m) (j : ℕ)
    {f : Reference.Space m → ℝ} (hf : Measurable f) :
    (∫ y, f y ∂projectedRestriction μ L j) = ∫ x, f (L x) ∂ballRestriction μ j := by
  rw [projectedRestriction, integral_map L.measurable.aemeasurable hf.aestronglyMeasurable]

lemma integral_projectedRestriction_tendsto (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (L : Reference.Space n →L[ℝ] Reference.Space m) {f : Reference.Space m → ℝ}
    (hf : Measurable f) (hi : Integrable f (μ.map L)) :
    Tendsto (fun j ↦ ∫ y, f y ∂projectedRestriction μ L j) atTop (𝓝 (∫ y, f y ∂μ.map L)) := by
  have h := integral_ballRestriction_tendsto (hi.comp_aemeasurable L.measurable.aemeasurable)
  simpa only [integral_projectedRestriction μ L _ hf,
    integral_map L.measurable.aemeasurable hf.aestronglyMeasurable, Function.comp_def] using h

lemma eventually_projectedRestriction_probability (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (L : Reference.Space n →L[ℝ] Reference.Space m) :
    ∀ᶠ j in atTop, IsProbabilityMeasure (projectedRestriction μ L j) := by
  filter_upwards [eventually_ballRestriction_probability μ] with j hj
  letI := hj
  exact Measure.isProbabilityMeasure_map L.measurable.aemeasurable

lemma projectedRestriction_compactlySupported (μ : Measure (Reference.Space n))
    (L : Reference.Space n →L[ℝ] Reference.Space m) (j : ℕ) :
    Reference.compactlySupported (projectedRestriction μ L j) :=
  LogConcaveLinearImages.compactlySupported_map (ballRestriction_compactlySupported μ j) L.toLinearMap

lemma eventually_projectedRestriction_logconcave {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (L : Reference.Space n →L[ℝ] Reference.Space m)
    (hL : Function.Surjective L) :
    ∀ᶠ j in atTop, Reference.logconcave (projectedRestriction μ L j) := by
  filter_upwards [eventually_ballRestriction_logconcave hl] with j hj
  exact LogConcaveLinearImages.logconcave_map_surjective (ballRestriction_compactlySupported μ j)
    hj L.toLinearMap hL

lemma meanVector_projectedRestriction_tendsto (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (L : Reference.Space n →L[ℝ] Reference.Space m)
    (hX : ∀ i : Fin m, Integrable (fun y : Reference.Space m ↦ y i) (μ.map L)) :
    Tendsto (fun j ↦ meanVector (projectedRestriction μ L j) coordinates)
      atTop (𝓝 (meanVector (μ.map L) coordinates)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact integral_projectedRestriction_tendsto μ L
    (PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) i).measurable (hX i)

lemma center_projectedRestriction_tendsto (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (L : Reference.Space n →L[ℝ] Reference.Space m)
    (hX : ∀ i : Fin m, Integrable (fun y : Reference.Space m ↦ y i) (μ.map L)) :
    Tendsto (fun j ↦ center (projectedRestriction μ L j)) atTop (𝓝 (center (μ.map L))) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).symm.continuous.tendsto _ |>.comp
    (meanVector_projectedRestriction_tendsto μ L hX)

lemma reference_covariance_projectedRestriction_tendsto (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (L : Reference.Space n →L[ℝ] Reference.Space m)
    (hX : ∀ i : Fin m, MemLp (fun y : Reference.Space m ↦ y i) 2 (μ.map L)) :
    Tendsto (fun j ↦ Reference.covariance (projectedRestriction μ L j))
      atTop (𝓝 (Reference.covariance (μ.map L))) := by
  letI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  have hm := meanVector_projectedRestriction_tendsto μ L (fun i ↦ (hX i).integrable (by norm_num))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact (integral_projectedRestriction_tendsto μ L (by fun_prop) ((hX i).integrable_mul (hX j))).sub
    ((tendsto_pi_nhds.mp hm i).mul (tendsto_pi_nhds.mp hm j))

lemma eventually_projectedRestriction_covariance_posSemidef
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (L : Reference.Space n →L[ℝ] Reference.Space m) :
    ∀ᶠ j in atTop, (Reference.covariance (projectedRestriction μ L j)).PosSemidef := by
  filter_upwards [eventually_projectedRestriction_probability μ L] with j hj
  letI := hj
  exact Reference.covariance_posSemidef
    (compact_coordinates_memLp (projectedRestriction_compactlySupported μ L j))

lemma eventually_projectedRestriction_covariance_posDef
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (L : Reference.Space n →L[ℝ] Reference.Space m) (hiso : Reference.isotropic (μ.map L)) :
    ∀ᶠ j in atTop, (Reference.covariance (projectedRestriction μ L j)).PosDef := by
  letI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  apply eventually_posDef_of_tendsto_one _ (eventually_projectedRestriction_covariance_posSemidef μ L)
  rw [← hiso.2]
  exact reference_covariance_projectedRestriction_tendsto μ L (Reference.isotropic_coordinate_memLp hiso)

lemma eventually_projectedRestriction_root_norm_le_two [Nonempty (Fin m)]
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (L : Reference.Space n →L[ℝ] Reference.Space m) (hiso : Reference.isotropic (μ.map L)) :
    ∀ᶠ j in atTop, ‖root (Reference.covariance (projectedRestriction μ L j))‖ ≤ 2 := by
  letI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  apply eventually_root_norm_le_two _ (eventually_projectedRestriction_covariance_posSemidef μ L)
  rw [← hiso.2]
  exact reference_covariance_projectedRestriction_tendsto μ L (Reference.isotropic_coordinate_memLp hiso)

lemma eventually_projectedRestriction_center_norm_le_one
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (L : Reference.Space n →L[ℝ] Reference.Space m) (hiso : Reference.isotropic (μ.map L)) :
    ∀ᶠ j in atTop, ‖center (projectedRestriction μ L j)‖ ≤ 1 := by
  letI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  have hX := fun i ↦ (Reference.isotropic_coordinate_memLp hiso i).integrable (by norm_num)
  have hc : center (μ.map L) = 0 := (center_eq_mean hX).trans hiso.1
  have hm := (center_projectedRestriction_tendsto μ L hX).norm
  rw [hc, norm_zero] at hm
  exact (hm.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h ↦ h.le)

end GaussianTilt.Whitening
