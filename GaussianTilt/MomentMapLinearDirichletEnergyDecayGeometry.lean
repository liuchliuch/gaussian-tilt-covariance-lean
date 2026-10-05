import GaussianTilt.MomentMapLinearDirichletEnergyFromExcess

/-! # Genuine half-ball and full-ball frozen energy decay from excess -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def halfBallEnergyDecayConstant (n : ℕ) (K θ : ℝ) : ℝ :=
  2*K+4*(K+1)*volume.real (Metric.ball (0 : KernelSpace n) 1)/(campanatoHalfBallVolume n*θ^n)

lemma halfBallEnergyDecayConstant_pos [NeZero n] {K θ : ℝ} (hK : 0 < K) (hθ : 0 < θ) :
    0 < halfBallEnergyDecayConstant n K θ := by
  unfold halfBallEnergyDecayConstant
  have hc := campanatoHalfBallVolume_pos (n := n)
  have hV : 0 ≤ volume.real (Metric.ball (0 : KernelSpace n) 1) := ENNReal.toReal_nonneg
  positivity

/-- The common normal approximant supplied by H¹ frozen half-ball excess
decay also yields the genuine n-th-power local energy decay. -/
theorem halfBall_energy_decay_of_common_excess [NeZero n] {F : Type*} [NormedAddCommGroup F]
    (j : Fin n) (G : KernelSpace n → F) (p : F) {R θ K : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hK : 0 < K)
    (hG : MemLp G 2 (volume.restrict (upperCampanatoBall j 0 R)))
    (hExcess : ∀ r : ℝ, 0 < r → r ≤ θ*R →
      (∫ x in upperCampanatoBall j 0 r, ‖G x-p‖^2) ≤
        K*(r/R)^(n+2)*(∫ x in upperCampanatoBall j 0 R, ‖G x‖^2)) :
    ∀ r : ℝ, 0 < r → r ≤ θ*R →
      (∫ x in upperCampanatoBall j 0 r, ‖G x‖^2) ≤
        halfBallEnergyDecayConstant n K θ*(r/R)^n*(∫ x in upperCampanatoBall j 0 R, ‖G x‖^2) := by
  apply energy_decay_of_common_excess n volume (upperCampanatoBall j 0) G p hR hθ hθ1 hK
    campanatoHalfBallVolume_pos ENNReal.toReal_nonneg (upperCampanatoBall_finite j 0 R)
  · intro r hr hrR
    apply upperCampanatoBall_mono
    simpa only [dist_self,zero_add] using hrR
  · exact hG
  · exact upperCampanatoBall_volume_lower j 0 (by simp) (mul_pos hθ hR)
  · intro r hr hrt
    have hh := measureReal_mono (μ := (volume : Measure (KernelSpace n)))
      (show upperCampanatoBall j 0 r ⊆ Metric.ball 0 r from inter_subset_left) measure_ball_lt_top.ne
    rw [real_volume_euclidean_ball _ hr.le] at hh
    simpa only [mul_comm] using hh
  · exact hExcess

/-- The same real intermediate-volume argument on full balls. -/
theorem fullBall_energy_decay_of_common_excess [NeZero n] {F : Type*} [NormedAddCommGroup F]
    (a : KernelSpace n) (G : KernelSpace n → F) (p : F) {R θ K : ℝ}
    (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hK : 0 < K)
    (hG : MemLp G 2 (volume.restrict (Metric.ball a R)))
    (hExcess : ∀ r : ℝ, 0 < r → r ≤ θ*R →
      (∫ x in Metric.ball a r, ‖G x-p‖^2) ≤ K*(r/R)^(n+2)*(∫ x in Metric.ball a R, ‖G x‖^2)) :
    ∀ r : ℝ, 0 < r → r ≤ θ*R →
      (∫ x in Metric.ball a r, ‖G x‖^2) ≤
        (2*K+4*(K+1)/θ^n)*(r/R)^n*(∫ x in Metric.ball a R, ‖G x‖^2) := by
  let V := volume.real (Metric.ball (0 : KernelSpace n) 1)
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  have hh := energy_decay_of_common_excess n volume (fun r => Metric.ball a r) G p hR hθ hθ1 hK hV hV.le
    measure_ball_lt_top.ne (fun r _ hrR => Metric.ball_subset_ball hrR) hG
    (by rw [real_volume_euclidean_ball a (mul_pos hθ hR).le]; exact le_of_eq (mul_comm _ _))
    (fun r hr _ => by rw [real_volume_euclidean_ball a hr.le]; exact le_of_eq (mul_comm _ _)) hExcess
  intro r hr hrt
  convert hh r hr hrt using 1
  have he : 4*(K+1)*V/(V*θ^n) = 4*(K+1)/θ^n := by field_simp
  rw [he]

end GaussianTilt.MomentMapLinearDirichlet
