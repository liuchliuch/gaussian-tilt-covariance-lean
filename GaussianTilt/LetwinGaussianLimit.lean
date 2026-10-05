import GaussianTilt.LetwinGaussianCentering
import GaussianTilt.LetwinGaussianBudget

/-! # Removing genuine Gaussian smoothing by proved variance continuity -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ContDiff Topology
namespace GaussianTilt.Letwin

/-- A quantitative quadratic bound on all positive Gaussian noise scales
passes to the original law. The continuity is proved from actual fourth
moments; it is not a premise of this limit theorem. -/
theorem quadratic_variance_le_of_noisy_bounds {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x∈K)
    (T B : Matrix (Fin n) (Fin n) ℝ) (C E F : ℝ)
    (hbound : ∀ r : ℝ, 0<r → variance (matrixQuadratic B) (noisyMomentMeasure φ T r) ≤
      C+E*r^2+F*r^4) :
    variance (matrixQuadratic B) (linearMomentMeasure φ T) ≤ C := by
  let r := fun k : ℕ => ((k : ℝ)+1)⁻¹
  have hr : Tendsto r atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hv := (continuous_noisy_quadratic_variance hφ hK hgrad T B).continuousAt.tendsto.comp hr
  rw [noisyMomentMeasure_zero hφ T] at hv
  have hbudget : Tendsto (fun k => C+E*(r k)^2+F*(r k)^4) atTop (𝓝 C) := by
    convert ((tendsto_const_nhds (x := C)).add ((tendsto_const_nhds (x := E)).mul (hr.pow 2))).add
      ((tendsto_const_nhds (x := F)).mul (hr.pow 4)) using 1 <;> simp
  exact le_of_tendsto_of_tendsto hv hbudget (Eventually.of_forall fun k => hbound (r k) (by dsimp [r]; positivity))

end GaussianTilt.Letwin
