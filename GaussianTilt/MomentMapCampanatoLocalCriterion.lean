import GaussianTilt.MomentMapCampanatoLocalJets

/-! # Local C² Campanato criterion without convexity or assumed differentiability -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

theorem hasFDerivAt_linear_coefficients_of_uniform_remainder
    {u : E n → ℝ} (a : E n → ℝ) (p : E n → E n) (H : E n → E n →L[ℝ] E n)
    {U : Set (E n)} (hU : IsOpen U) {R C α : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hH : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w))
    (happrox : ∀ x ∈ U, ∀ z : E n, ‖z - x‖ ≤ R →
      |u z - quadraticJet (a x) (p x) x (H x) z| ≤ C * ‖z - x‖ ^ (2 + α))
    {x : E n} (hx : x ∈ U) : HasFDerivAt p (H x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  let L := C * (1 + (2 : ℝ) ^ (2 + α))
  have hc : Continuous (fun h : E n => L * ‖h‖ ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp continuous_norm)
  have hev : ∀ᶠ h : E n in 𝓝 0, L * ‖h‖ ^ α < ε :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa [Real.zero_rpow hα.ne'] using hε))
  have htrans : Tendsto (fun h : E n => x + h) (𝓝 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds.add tendsto_id : Tendsto (fun h : E n => x + h) (𝓝 0) (𝓝 (x + 0)))
  filter_upwards [hev, htrans (hU.mem_nhds hx), Metric.ball_mem_nhds (0 : E n) (half_pos hR)] with h he hxh hh
  have hn : 2 * ‖(x + h) - x‖ ≤ R := by
    have hh' : ‖h‖ < R / 2 := by simpa using hh
    simpa only [add_sub_cancel_left] using (show 2 * ‖h‖ ≤ R by linarith)
  have hb := linear_coefficients_remainder_of_uniform_remainder a p H hC hα hH happrox hxh hx hn
  simp only [add_sub_cancel_left] at hb
  have heq : p (x + h) - p x - H x h = p (x + h) - (p x + H x h) := by abel
  rw [heq]
  apply hb.trans
  by_cases hz : h = 0
  · simp [hz, Real.zero_rpow (by linarith : (1 : ℝ) + α ≠ 0)]
  · have hp : 0 < ‖h‖ := norm_pos_iff.mpr hz
    rw [add_comm (1 : ℝ) α, Real.rpow_add hp, Real.rpow_one]
    change L * (‖h‖ ^ α * ‖h‖) ≤ ε * ‖h‖
    nlinarith [mul_le_mul_of_nonneg_right he.le hp.le]

/-- Uniform actual quadratic approximations determine both derivatives;
only openness of the region of centers is needed. -/
theorem contDiffOn_two_of_uniform_quadratic_remainders_local
    {u : E n → ℝ} (a : E n → ℝ) (p : E n → E n) (H : E n → E n →L[ℝ] E n)
    {U : Set (E n)} (hU : IsOpen U) {R C α : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hH : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w))
    (happrox : ∀ x ∈ U, ∀ z : E n, ‖z - x‖ ≤ R →
      |u z - quadraticJet (a x) (p x) x (H x) z| ≤ C * ‖z - x‖ ^ (2 + α)) :
    ContDiffOn ℝ 2 u U ∧
      (∀ x ∈ U, a x = u x ∧ p x = gradient u x) ∧
      (∀ x ∈ U, HasFDerivAt (gradient u) (H x) x) := by
  have hfirst := fun x hx => hasFDerivAt_of_quadratic_holder_remainder
    (a x) (p x) x (H x) hR hC hα (happrox x hx)
  have hsecond : ∀ x ∈ U, HasFDerivAt p (H x) x := fun x hx => hasFDerivAt_linear_coefficients_of_uniform_remainder
    a p H hU hR hC hα hH happrox hx
  have hcont := continuousOn_quadratic_coefficients_of_uniform_remainder a p H hR hC hα hH happrox
  have hpgrad : ∀ x ∈ U, p x = gradient u x := by
    intro x hx
    have he := congrArg (InnerProductSpace.toDual ℝ (E n)).symm (hfirst x hx).2.fderiv
    simpa only [gradient, LinearIsometryEquiv.symm_apply_apply] using he.symm
  have hpc : ContDiffOn ℝ 1 p U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hsecond x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact hcont.congr (fun x hx => (hsecond x hx).fderiv)
  refine ⟨?_, fun x hx => ⟨(hfirst x hx).1, hpgrad x hx⟩, ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hfirst x hx).2.differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · exact ((InnerProductSpace.toDual ℝ (E n)).toContinuousLinearEquiv.contDiff.comp_contDiffOn hpc).congr
        (fun x hx => (hfirst x hx).2.fderiv)
  · intro x hx
    have he : gradient u =ᶠ[𝓝 x] p := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hpgrad y hy).symm
    exact (hsecond x hx).congr_of_eventuallyEq he

end GaussianTilt.MomentMapRegularity
