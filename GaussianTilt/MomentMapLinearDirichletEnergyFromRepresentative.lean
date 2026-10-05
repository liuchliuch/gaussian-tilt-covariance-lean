import GaussianTilt.MomentMapLinearDirichletCampanatoL2Interpolation

/-! # Actual rⁿ energy bounds from the constructed continuous representative -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Compactness of the genuinely constructed gradient representative
upgrades the original weak-field energy to order rⁿ uniformly in centers.
This is the input for recovering the full Hölder exponent on a smaller patch. -/
theorem exists_local_energy_bound_of_continuous_representative [NeZero n]
    {F : Type*} [NormedAddCommGroup F] (j : Fin n) (W L : KernelSpace n → F) {R : ℝ}
    (hR : 0 < R) (hW : MemLp W 2 (volume.restrict (upperCampanatoBall j 0 (2*R))))
    (hL : ContinuousOn L (Metric.closedBall 0 (R/4) ∩ {x | 0 ≤ x j}))
    (hLW : ∀ᵐ x ∂volume, ‖x‖ ≤ R/4 → 0 < x j → L x=W x) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : KernelSpace n, ‖x‖ ≤ R/8 → 0 ≤ x j →
      ∀ r : ℝ, 0 < r → r ≤ R/8 →
        (∫ z in upperCampanatoBall j x r, ‖W z‖^2) ≤ M*r^n := by
  let S : Set (KernelSpace n) := Metric.closedBall 0 (R/4) ∩ {x | 0 ≤ x j}
  have hSc : IsCompact S := (isCompact_closedBall (0 : KernelSpace n) (R/4)).inter_right
    (isClosed_le continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous)
  obtain ⟨B,hB⟩ := hSc.exists_bound_of_continuousOn hL
  let D := max B 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let V := volume.real (Metric.ball (0 : KernelSpace n) 1)
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  refine ⟨D^2*V,by positivity,?_⟩
  intro x hx hxj r hr hrR
  have hsub : upperCampanatoBall j x r ⊆ S := by
    intro z hz
    have hn : ‖z-x‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hz.1
    have ht : ‖z‖ ≤ ‖z-x‖+‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (z-x) x
    refine ⟨?_,show 0 ≤ z j from hz.2.le⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith
  have hI : IntegrableOn (fun z => ‖W z‖^2) (upperCampanatoBall j x r) := by
    simpa only [sub_zero] using local_memLp_square_error_halfBall j hW hR (by linarith : r ≤ R)
      (by linarith : ‖x‖ ≤ R/4) (0:F)
  have hconst : IntegrableOn (fun _ : KernelSpace n => D^2) (upperCampanatoBall j x r) :=
    integrableOn_const (upperCampanatoBall_finite j x r)
  have hpoint : ∀ᵐ z ∂volume.restrict (upperCampanatoBall j x r), ‖W z‖^2 ≤ D^2 := by
    filter_upwards [ae_restrict_of_ae hLW,ae_restrict_mem (isOpen_upperCampanatoBall j x r).measurableSet] with z hz hzΩ
    have hzS := hsub hzΩ
    have hzn : ‖z‖ ≤ R/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hzS.1
    rw [← hz hzn hzΩ.2]
    exact (sq_le_sq₀ (norm_nonneg _) hD.le).mpr ((hB z hzS).trans (le_max_left _ _))
  have he := integral_mono_ae hI hconst hpoint
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at he
  have hvol := measureReal_mono (μ := (volume : Measure (KernelSpace n)))
    (show upperCampanatoBall j x r ⊆ Metric.ball x r from inter_subset_left) measure_ball_lt_top.ne
  rw [real_volume_euclidean_ball x hr.le] at hvol
  have hv := mul_le_mul_of_nonneg_right hvol (sq_nonneg D)
  nlinarith

end GaussianTilt.MomentMapLinearDirichlet
