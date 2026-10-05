import GaussianTilt.EllipticRegularitySobolev
import GaussianTilt.EllipticRegularitySobolevTransport

/-! # Actual compact local regularity in the original weighted Sobolev graph -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma tsupport_ellipticCutoff_subset {n : ℕ} {R : ℝ} (hR : 0 < R) :
    tsupport (ellipticCutoff n R) ⊆ Metric.closedBall 0 (2 * R) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hn
  apply hx
  apply ellipticCutoff_eq_zero hR
  exact le_of_lt (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn)

lemma ellipticCutoff_one_on_tsupport {n : ℕ} {R : ℝ} (hR : 0 < R) :
    ∀ x ∈ tsupport (ellipticCutoff n R), ellipticCutoff n (2 * R) x = 1 := by
  intro x hx
  apply ellipticCutoff_eq_one (by positivity)
  simpa only [Metric.mem_closedBall, dist_zero_right] using tsupport_ellipticCutoff_subset hR hx

/-- Every compact localization of the rough annihilator is an actual
weighted H¹ function too; this is proved by compact density transport. -/
theorem weighted_generator_orthogonal_local_weighted_H1 {n : ℕ}
    {φ h χ : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hh : MemLp h 2 (potentialMeasure φ))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (horth : ∀ f : CoordinateSpace n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, h x * weightedLaplacian φ f x ∂potentialMeasure φ) = 0) :
    ∃ u : weightedSobolev (potentialMeasure φ),
      u.1 0 =ᵐ[potentialMeasure φ] fun x => χ x * h x := by
  obtain ⟨u, hu⟩ := weighted_generator_orthogonal_local_H1 hφ hh hχ hχc horth
  obtain ⟨R, hR, hKR⟩ := hχc.isBounded.subset_closedBall_lt 0 (0 : CoordinateSpace n)
  obtain ⟨v, hv, -⟩ := exists_weightedSobolev_mul_from_volume hφ.continuous
    (ellipticCutoff_contDiff n R) (ellipticCutoff_compact n hR.ne') u
  have hu0 : u.1 0 =ᵐ[volume] fun x => χ x * h x := by
    change u.1 0 = (memLp_compact_mul_of_potential hφ.continuous hh hχ.continuous hχc).toLp
      (fun x => χ x * h x) at hu
    rw [hu]
    exact (memLp_compact_mul_of_potential hφ.continuous hh hχ.continuous hχc).coeFn_toLp
  refine ⟨v, ?_⟩
  filter_upwards [hv, (potentialMeasure_absolutelyContinuous φ).ae_eq hu0] with x hvx hux
  rw [hvx, hux]
  by_cases hx : x ∈ tsupport χ
  · rw [ellipticCutoff_eq_one hR (by simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hx), one_mul]
  · have hz : χ x = 0 := Function.notMem_support.mp (fun hs => hx (subset_closure hs))
    simp [hz]

end GaussianTilt.Letwin
