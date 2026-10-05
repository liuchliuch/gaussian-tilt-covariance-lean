import GaussianTilt.LetwinGaussianLimit

/-! # Exact moment-law transport for the final regular variance theorem -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff
namespace GaussianTilt.Letwin

lemma covarianceMatrix_momentMeasure {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    covarianceMatrix (momentMeasure φ) id = covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) := by
  ext i j
  rw [covarianceMatrix, momentMeasure, covariance_map_fun
    (show AEStronglyMeasurable (fun x : CoordinateSpace n => id x i) _ from (continuous_apply i).aestronglyMeasurable)
    (show AEStronglyMeasurable (fun x : CoordinateSpace n => id x j) _ from (continuous_apply j).aestronglyMeasurable)
    (continuous_coordinateGradient hφ).measurable.aemeasurable]
  rfl

lemma momentPotential_covariance_of_target {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {μ : Measure (CoordinateSpace n)}
    (hmap : momentMeasure φ=μ) (hiso : covarianceMatrix μ id=1) :
    covarianceMatrix (potentialMeasure φ) (coordinateGradient φ)=1 := by
  rw [← covarianceMatrix_momentMeasure hφ, hmap, hiso]

lemma variance_momentMeasure {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (B : Matrix (Fin n) (Fin n) ℝ) :
    variance (matrixQuadratic B) (momentMeasure φ) =
      variance (fun x => matrixQuadratic B (coordinateGradient φ x)) (potentialMeasure φ) := by
  rw [momentMeasure, variance_map (contDiff_matrixQuadratic B).continuous.aemeasurable
    (continuous_coordinateGradient hφ).measurable.aemeasurable]
  rfl

/-- The sign-coordinate variance is exactly the variance of the original
quadratic under the target moment law, not merely a comparison. -/
lemma variance_signCoordinates_eq_target {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {μ : Measure (CoordinateSpace n)} (hmap : momentMeasure φ=μ)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    variance (matrixQuadratic (spectralSign hB)) (linearMomentMeasure φ (spectralMagnitudeRoot hB)) =
      variance (matrixQuadratic B) μ := by
  rw [variance_spectralCoordinates hφ hB, ← variance_momentMeasure hφ B, hmap]

end GaussianTilt.Letwin
