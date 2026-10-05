import GaussianTilt.MomentMapCampanatoHolderJets

/-! # Uniform quadratic jets give actual derivatives without global convexity -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

theorem linear_coefficients_remainder_of_uniform_remainder
    {u : E n → ℝ} (a : E n → ℝ) (p : E n → E n) (H : E n → E n →L[ℝ] E n)
    {U : Set (E n)} {R C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hH : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w))
    (happrox : ∀ x ∈ U, ∀ z : E n, ‖z - x‖ ≤ R →
      |u z - quadraticJet (a x) (p x) x (H x) z| ≤ C * ‖z - x‖ ^ (2 + α))
    {x y : E n} (hx : x ∈ U) (hy : y ∈ U) (hxy : 2 * ‖x - y‖ ≤ R) :
    ‖p x - (p y + H y (x - y))‖ ≤ (C * (1 + (2 : ℝ) ^ (2 + α))) * ‖x - y‖ ^ (1 + α) := by
  by_cases heq : x = y
  · subst y
    simp only [sub_self, map_zero, add_zero, norm_zero, Real.zero_rpow (by linarith : (1 : ℝ) + α ≠ 0), mul_zero, le_refl]
  let d := ‖x - y‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  have hα2 : 0 ≤ 2 + α := by linarith
  have ha : ∀ h : E n, ‖h‖ ≤ d →
      |u (x + h) - quadraticJet (a x) (p x) 0 (H x) h| ≤ C * d ^ (2 + α) := by
    intro h hh
    have hb := happrox x hx (x + h) (by simpa only [add_sub_cancel_left] using (hh.trans (by dsimp [d] at *; linarith)))
    simp only [quadraticJet, add_sub_cancel_left, sub_zero] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg h) hh hα2) hC)
  have hb : ∀ h : E n, ‖h‖ ≤ d →
      |u (x + h) - quadraticJet (quadraticJet (a y) (p y) y (H y) x)
        (p y + H y (x - y)) 0 (H y) h| ≤ C * (2 * d) ^ (2 + α) := by
    intro h hh
    have hdist : ‖x + h - y‖ ≤ 2 * d := by
      calc
        ‖x + h - y‖ = ‖(x - y) + h‖ := by congr 1; abel
        _ ≤ ‖x - y‖ + ‖h‖ := norm_add_le _ _
        _ ≤ 2 * d := by dsimp [d] at *; linarith
    rw [← quadraticJet_recenter (a y) (p y) x y h (H y) (hH y hy)]
    exact (happrox y hy (x + h) (hdist.trans hxy)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hdist hα2) hC)
  have he := (quadraticJet_coherence (f := fun h => u (x + h))
    (a x) (quadraticJet (a y) (p y) y (H y) x) (p x) (p y + H y (x - y))
    (H x) (H y) (hH x hx) (hH y hy) hd (by positivity) (by positivity) ha hb).2.1
  have heq : (C * d ^ (2 + α) + C * (2 * d) ^ (2 + α)) / d =
      (C * (1 + (2 : ℝ) ^ (2 + α))) * d ^ (1 + α) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le,
      show (2 : ℝ) + α = 1 + (1 + α) by ring, Real.rpow_add hd, Real.rpow_one]
    field_simp
    <;> ring
  rwa [heq] at he


/-- The first derivative follows from the actual quadratic remainder alone. -/
theorem hasFDerivAt_of_quadratic_holder_remainder
    {u : E n → ℝ} (a : ℝ) (p x : E n) (H : E n →L[ℝ] E n)
    {R C α : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (happrox : ∀ z : E n, ‖z - x‖ ≤ R →
      |u z - quadraticJet a p x H z| ≤ C * ‖z - x‖ ^ (2 + α)) :
    a = u x ∧ HasFDerivAt u (InnerProductSpace.toDual ℝ (E n) p) x := by
  have ha : a = u x := by
    have hb := happrox x (by simpa using hR.le)
    simp only [quadraticJet, sub_self, map_zero, inner_zero_right, inner_zero_left,
      add_zero, mul_zero, norm_zero, Real.zero_rpow (by linarith : (2 : ℝ) + α ≠ 0)] at hb
    exact (sub_eq_zero.mp (abs_nonpos_iff.mp hb)).symm
  refine ⟨ha, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hc : Continuous (fun h : E n => C * ‖h‖ ^ (1 + α) + (1 / 2 : ℝ) * ‖H‖ * ‖h‖) := by
    exact (continuous_const.mul ((Real.continuous_rpow_const (by linarith)).comp continuous_norm)).add
      (continuous_const.mul continuous_norm)
  have hev : ∀ᶠ h : E n in 𝓝 0, C * ‖h‖ ^ (1 + α) + (1 / 2 : ℝ) * ‖H‖ * ‖h‖ < ε :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa only [norm_zero, Real.zero_rpow (by linarith : (1 : ℝ) + α ≠ 0), mul_zero, add_zero] using hε))
  filter_upwards [hev, Metric.ball_mem_nhds (0 : E n) hR] with h he hh
  have hhn : ‖h‖ ≤ R := (by simpa only [Metric.mem_ball, dist_zero_right] using hh : ‖h‖ < R).le
  have ht := happrox (x + h) (by simpa only [add_sub_cancel_left] using hhn)
  simp only [add_sub_cancel_left] at ht
  have hi : |inner ℝ (H h) h| ≤ ‖H‖ * ‖h‖ ^ 2 := by
    exact (abs_real_inner_le_norm _ _).trans (by
      have hb := mul_le_mul_of_nonneg_right (H.le_opNorm h) (norm_nonneg h)
      nlinarith)
  have hb : |u (x + h) - u x - inner ℝ p h| ≤ C * ‖h‖ ^ (2 + α) + (1 / 2 : ℝ) * ‖H‖ * ‖h‖ ^ 2 := by
    calc
      _ = |(u (x + h) - quadraticJet a p x H (x + h)) + (1 / 2 : ℝ) * inner ℝ (H h) h| := by
        congr 1
        simp only [quadraticJet, add_sub_cancel_left, ha]
        ring
      _ ≤ |u (x + h) - quadraticJet a p x H (x + h)| + |(1 / 2 : ℝ) * inner ℝ (H h) h| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact add_le_add ht (by nlinarith)
  change |u (x + h) - u x - inner ℝ p h| ≤ ε * ‖h‖
  apply hb.trans
  by_cases hz : h = 0
  · simp only [hz, norm_zero, Real.zero_rpow (by linarith : (2 : ℝ) + α ≠ 0), zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, le_refl]
  · have hp : 0 < ‖h‖ := norm_pos_iff.mpr hz
    rw [show (2 : ℝ) + α = (1 + α) + 1 by ring, Real.rpow_add hp, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_right he.le hp.le]

end GaussianTilt.MomentMapRegularity
