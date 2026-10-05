import GaussianTilt.LetwinQuadraticDuality
import GaussianTilt.LinearImageDensity

/-! # Genuine law-level side conditions for the regular variance application -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

def coordinateMatrixEquiv {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) :
    CoordinateSpace n ≃L[ℝ] CoordinateSpace n :=
  (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) T (isUnit_iff_ne_zero.mpr hT)).toContinuousLinearEquiv

@[simp] lemma coordinateMatrixEquiv_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (hT : T.det ≠ 0) (x : CoordinateSpace n) : coordinateMatrixEquiv T hT x = T *ᵥ x := by
  change Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n)) T x = T *ᵥ x
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

lemma linearMomentMeasure_eq_map {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (T : Matrix (Fin n) (Fin n) ℝ) :
    linearMomentMeasure φ T = (momentMeasure φ).map (coordinateMatrixMap T) := by
  rw [momentMeasure, Measure.map_map (coordinateMatrixMap T).continuous.measurable
    (continuous_coordinateGradient hφ).measurable]
  rfl

/-- A genuine logconcave density is preserved under the invertible linear
coordinates used in the sign decomposition. -/
theorem linearMomentMeasure_logconcaveDensity {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {f : CoordinateSpace n → ℝ}
    (hf : LogConcaveMarginal.IsLogConcave f) (hfm : Measurable f)
    (hμ : momentMeasure φ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) :
    ∃ g : CoordinateSpace n → ℝ, LogConcaveMarginal.IsLogConcave g ∧ Measurable g ∧
      linearMomentMeasure φ T = volume.withDensity (fun z => ENNReal.ofReal (g z)) := by
  obtain ⟨c, _hc, hg, hgm, hmap⟩ := LinearImageDensity.exists_density_map_linearEquiv
    (coordinateMatrixEquiv T hT) volume volume hf hfm
  refine ⟨_, hg, hgm, ?_⟩
  rw [linearMomentMeasure_eq_map hφ T, hμ]
  convert hmap using 1

/-- Compact support of the actual transported law follows from the actual
compact gradient image, rather than an assumed compactness of the density. -/
theorem linearMomentMeasure_compactSupport {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (T : Matrix (Fin n) (Fin n) ℝ) :
    ∃ L : Set (CoordinateSpace n), IsCompact L ∧ (linearMomentMeasure φ T) Lᶜ = 0 := by
  let L := coordinateMatrixMap T '' K
  have hL : IsCompact L := hK.image (coordinateMatrixMap T).continuous
  refine ⟨L, hL, ?_⟩
  rw [linearMomentMeasure, Measure.map_apply (continuous_linearMomentMap hφ T).measurable
    hL.isClosed.measurableSet.compl]
  have hp : (fun x => T *ᵥ coordinateGradient φ x) ⁻¹' Lᶜ = ∅ := by
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact ⟨coordinateGradient φ x, hgrad x, rfl⟩
  rw [hp, measure_empty]

end GaussianTilt.Letwin
