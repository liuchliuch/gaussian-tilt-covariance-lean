import GaussianTilt.MomentMapRegularityImprovementCenteredGeometry

/-! # Both affine coordinate norms from actual inner and outer section balls -/
noncomputable section
open Set Metric
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma operator_norm_le_of_ball_bound (L : E n →L[ℝ] E n) {r R : ℝ}
    (hr : 0 < r) (hR : 0≤R) (hbound : ∀ y, ‖y‖≤r → ‖L y‖≤R) : ‖L‖≤R/r := by
  apply L.opNorm_le_bound (div_nonneg hR hr.le)
  intro v
  by_cases hv : v=0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 < r/‖v‖ := div_pos hr hn
  have hy : ‖(r/‖v‖) • v‖=r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,div_mul_cancel₀ _ hn.ne']
  have hh := hbound ((r/‖v‖) • v) hy.le
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hh
  have hm : r*‖L v‖≤R*‖v‖ := by
    apply (div_le_iff₀ hn).mp
    simpa only [div_mul_eq_mul_div] using hh
  have hfinal : ‖L v‖≤(R*‖v‖)/r := (le_div_iff₀ hr).mpr (by nlinarith)
  simpa only [div_mul_eq_mul_div] using hfinal

/-- The inverse normalization contracts as the genuine source section shrinks. -/
lemma inverse_coordinate_norm_from_section_balls (T : E n ≃L[ℝ] E n)
    {S : Set (E n)} {x : E n} {r ε : ℝ} (hr : 0 < r) (hε : 0≤ε)
    (hinner : closedBall (0:E n) r⊆(fun y=>T (y-x)) '' S)
    (houter : S⊆closedBall x ε) : ‖(T.symm : E n →L[ℝ] E n)‖≤ε/r := by
  apply operator_norm_le_of_ball_bound _ hr hε
  intro y hy
  obtain ⟨z,hz,hzy⟩ := hinner (by simpa only [mem_closedBall,dist_zero_right] using hy)
  have he : T.symm y=z-x := by rw [← hzy,T.symm_apply_apply]
  change ‖T.symm y‖≤ε
  rw [he]
  exact houter hz

/-- A genuine source inner ball prevents the forward normalization from
blowing up when the source center ranges over a fixed compact set. -/
lemma coordinate_norm_from_section_balls (T : E n ≃L[ℝ] E n)
    {S : Set (E n)} {x : E n} {r R : ℝ} (hr : 0 < r) (hR : 0≤R)
    (hinner : closedBall x r⊆S)
    (houter : (fun y=>T (y-x)) '' S⊆closedBall (0:E n) R) :
    ‖(T : E n →L[ℝ] E n)‖≤R/r := by
  apply operator_norm_le_of_ball_bound _ hr hR
  intro y hy
  have hxy : x+y∈S := hinner (by simpa [dist_eq_norm,add_sub_cancel_left] using hy)
  have hh : T y∈closedBall (0:E n) R := houter ⟨x+y,hxy,by simp⟩
  simpa only [mem_closedBall,dist_zero_right,ContinuousLinearEquiv.coe_apply] using hh

end GaussianTilt.MomentMapRegularity
