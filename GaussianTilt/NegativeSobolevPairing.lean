import GaussianTilt.NegativeSobolevDuality

/-! # The actual generator test estimate behind H⁻¹ duality -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- Pairing with every compact smooth generator is controlled by the negative
Sobolev bounds on the actual derivatives of the observable. -/
theorem generator_pairing_sq_le {n : ℕ} {φ f u : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef)
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hB : ∀ i, CompactNegativeSobolevBound (potentialMeasure φ)
      (coordinateDerivative i f) (C i)) :
    (∫ x, f x * weightedLaplacian φ u x ∂potentialMeasure φ)^2 ≤
      (∑ i, C i^2) * ∫ x, (weightedLaplacian φ u x)^2 ∂potentialMeasure φ := by
  let μ := potentialMeasure φ
  let E := fun i => ∫ x, gradientSquare (coordinateDerivative i u) x ∂μ
  let a := fun i => ∫ x, coordinateDerivative i f x * coordinateDerivative i u x ∂μ
  have hdc (i : Fin n) : HasCompactSupport (coordinateDerivative i u) :=
    huc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  have hdi (i : Fin n) : Integrable
      (fun x => coordinateDerivative i u x * coordinateDerivative i f x) μ :=
    ((smooth_coordinateDerivative hu i).continuous.mul
      (smooth_coordinateDerivative hf i).continuous).integrable_of_hasCompactSupport (hdc i).mul_right
  have hgreen := integral_divergenceDiffusion_mul_compact_left (A := fun _ => 1)
    (contDiff_infty.mp hφ 1) (fun _ _ => contDiff_const) (contDiff_infty.mp hu 2)
    (contDiff_infty.mp hf 1) huc
  have hp : (∫ x, f x * weightedLaplacian φ u x ∂μ) = -(∑ i, a i) := by
    change (∫ x, weightedLaplacian φ u x * f x ∂μ) =
      -(∫ x, diffusionGamma (fun _ => 1) u f x ∂μ) at hgreen
    simp only [diffusionGamma_one] at hgreen
    rw [integral_finset_sum _ (fun i _ => hdi i)] at hgreen
    simpa only [a, mul_comm] using hgreen
  have hb : (∑ i, a i)^2 ≤ (∑ i, C i^2) * ∑ i, E i :=
    sum_pairings_sq_le a C E hC
      (fun i => integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (fun i => (hB i).pairing_le (hC i) (smooth_coordinateDerivative hu i) (hdc i))
  have hbochner := sum_integral_gradientSquare_le_laplacian_sq hφ hu huc hH
  rw [hp, neg_sq]
  exact hb.trans (mul_le_mul_of_nonneg_left hbochner
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- A bounded pairing estimate on a linear core passes to its actual norm
closure.  This is a general Hilbert-space fact, not a range-density premise. -/
theorem sq_norm_le_of_core_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : Submodule ℝ H) (f : H) (B : ℝ)
    (hB : 0 ≤ B) (hf : f ∈ K.topologicalClosure)
    (hcore : ∀ v ∈ K, (inner ℝ f v)^2 ≤ B * ‖v‖^2) : ‖f‖^2 ≤ B := by
  have hc : IsClosed {v : H | (inner ℝ f v)^2 ≤ B * ‖v‖^2} :=
    isClosed_le ((continuous_const.inner continuous_id).pow 2)
      (continuous_const.mul (continuous_norm.pow 2))
  have hfull : ∀ v ∈ K.topologicalClosure, (inner ℝ f v)^2 ≤ B * ‖v‖^2 :=
    fun v hv => (closure_minimal hcore hc) hv
  have h := hfull f hf
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [sq_nonneg ‖f‖]

end GaussianTilt.Letwin
