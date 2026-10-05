import GaussianTilt.MomentMapLinearDirichletCenteredLoadScale
import GaussianTilt.MomentMapLinearDirichletHalfBallGeometry
import GaussianTilt.MomentMapLinearDirichletCoordinates

/-! # Actual Euclidean-volume forcing constants in raw coordinate domains -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Coordinate transport preserves the true Lebesgue volume. Thus a raw
coordinate domain contained in a Euclidean ball has the exact rⁿ bound. -/
theorem coordinate_domain_real_volume_le [NeZero n] {Ω : Set (CoordinateSpace n)}
    (hΩ : MeasurableSet Ω) {r : ℝ} (hr : 0 ≤ r)
    (hball : ∀ x ∈ Ω, ‖(dirichletCoordinateEquiv n).symm x‖ < r) :
    volume.real Ω ≤ volume.real (Metric.ball (0 : KernelSpace n) 1)*r^n := by
  let L := dirichletCoordinateEquiv n
  have hμ : MeasurePreserving L volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hsub : L ⁻¹' Ω ⊆ Metric.ball (0 : KernelSpace n) r := by
    intro x hx
    rw [Metric.mem_ball,dist_zero_right]
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hball (L x) hx
  have he : (volume : Measure (KernelSpace n)).real (L ⁻¹' Ω) = volume.real Ω := by
    exact congrArg ENNReal.toReal (hμ.measure_preimage hΩ.nullMeasurableSet)
  have hb := measureReal_mono (μ := (volume : Measure (KernelSpace n))) hsub measure_ball_lt_top.ne
  rw [he,real_volume_euclidean_ball _ hr] at hb
  simpa only [mul_comm] using hb

lemma coordinateHalfBall_real_volume_le [NeZero n] (j : Fin n) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coordinateHalfBall j r) ≤ volume.real (Metric.ball (0 : KernelSpace n) 1)*r^n := by
  apply coordinate_domain_real_volume_le (isOpen_coordinateHalfBall j r).measurableSet hr
  intro x hx
  exact hx.1

/-- The centered scalar/vector coefficient on a genuine half-ball has the
correct actual dimensional forcing power, with its fixed ball-volume constant. -/
theorem halfBall_centered_load_coefficient_sq_bound [NeZero n] (j : Fin n)
    {r F H β : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ((2*r*F+(n:ℝ)*H*r^β)*Real.sqrt (volume.real (coordinateHalfBall j r)))^2 ≤
      ((2*F+(n:ℝ)*H)^2*volume.real (Metric.ball (0 : KernelSpace n) 1))*r^((n:ℝ)+2*β) :=
  centered_load_coefficient_sq_bound hr hr1 hF hH hβ hβ1 ENNReal.toReal_nonneg
    (coordinateHalfBall_real_volume_le j hr.le)

end GaussianTilt.MomentMapLinearDirichlet
