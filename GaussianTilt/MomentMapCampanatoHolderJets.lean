import GaussianTilt.MomentMapCampanatoJets

/-! # Hölder continuity of actual quadratic coefficients

Overlapping Taylor balls and polarization prove the Hölder coefficient
bound. Continuity of the putative Hessian is not assumed.
-/
noncomputable section
open Set Filter
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma quadraticJet_recenter (a : ℝ) (p x y h : E n) (H : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w)) :
    quadraticJet a p y H (x + h) =
      quadraticJet (quadraticJet a p y H x) (p + H (x - y)) 0 H h := by
  have he := quadraticJet_remainder a p y x (x + h) H hH
  simp only [add_sub_cancel_left] at he
  simp only [quadraticJet, sub_zero]
  unfold quadraticJet at he
  linarith

/-- Uniform positive-order quadratic remainders force Hölder continuity of
the true quadratic coefficients, proved by overlapping balls. -/
theorem quadratic_coefficients_holder_of_uniform_remainder
    {u : E n → ℝ} (a : E n → ℝ) (p : E n → E n) (H : E n → E n →L[ℝ] E n)
    {U : Set (E n)} {R C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hH : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w))
    (happrox : ∀ x ∈ U, ∀ z : E n, ‖z - x‖ ≤ R →
      |u z - quadraticJet (a x) (p x) x (H x) z| ≤ C * ‖z - x‖ ^ (2 + α))
    {x y : E n} (hx : x ∈ U) (hy : y ∈ U) (hxy : 2 * ‖x - y‖ ≤ R) :
    ‖H x - H y‖ ≤ (4 * C * (1 + (2 : ℝ) ^ (2 + α))) * ‖x - y‖ ^ α := by
  by_cases heq : x = y
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
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
    (H x) (H y) (hH x hx) (hH y hy) hd (by positivity) (by positivity) ha hb).2.2
  have heq : 4 * (C * d ^ (2 + α) + C * (2 * d) ^ (2 + α)) / d ^ 2 =
      (4 * C * (1 + (2 : ℝ) ^ (2 + α))) * d ^ α := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le,
      Real.rpow_add hd, Real.rpow_two]
    field_simp
    <;> ring
  rwa [heq] at he

/-- The continuity of the quadratic coefficient field follows from the
uniform remainders; it is not an extra regularity input. -/
theorem continuousOn_quadratic_coefficients_of_uniform_remainder
    {u : E n → ℝ} (a : E n → ℝ) (p : E n → E n) (H : E n → E n →L[ℝ] E n)
    {U : Set (E n)} {R C α : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hH : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w))
    (happrox : ∀ x ∈ U, ∀ z : E n, ‖z - x‖ ≤ R →
      |u z - quadraticJet (a x) (p x) x (H x) z| ≤ C * ‖z - x‖ ^ (2 + α)) :
    ContinuousOn H U := by
  intro x hx
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  let K := 4 * C * (1 + (2 : ℝ) ^ (2 + α))
  have ht : Tendsto (fun y : E n => K * ‖y - x‖ ^ α) (𝓝[U] x) (𝓝 0) := by
    have hc : Continuous (fun y : E n => K * ‖y - x‖ ^ α) :=
      continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
        ((continuous_id.sub continuous_const).norm))
    simpa only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using
      (hc.continuousAt (x := x)).continuousWithinAt.tendsto (s := U)
  apply squeeze_zero' (Eventually.of_forall (fun y => norm_nonneg (H y - H x))) ?_ ht
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ y in 𝓝[U] x, y ∈ Metric.ball x (R / 2) from
      nhdsWithin_le_nhds (Metric.ball_mem_nhds x (half_pos hR)))] with y hy hnear
  have hd : 2 * ‖y - x‖ ≤ R := by
    have h : ‖y - x‖ < R / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hnear
    linarith
  exact quadratic_coefficients_holder_of_uniform_remainder a p H hC hα hH happrox hy hx hd

/-- Uniform Hölder Taylor approximations yield actual C² and the actual
Hölder derivative field, with no continuity or Hessian premise. -/
theorem contDiffOn_two_of_uniform_holder_quadratic_remainders
    {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    {U : Set (E n)} (hU : IsOpen U) (H : E n → E n →L[ℝ] E n)
    {R C α : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hH : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w))
    (happrox : ∀ x ∈ U, ∀ z : E n, ‖z - x‖ ≤ R →
      |u z - quadraticJet (u x) (gradient u x) x (H x) z| ≤ C * ‖z - x‖ ^ (2 + α)) :
    ContDiffOn ℝ 2 u U ∧
      ∀ x ∈ U, HasFDerivAt (gradient u) (H x) x := by
  have hcont := continuousOn_quadratic_coefficients_of_uniform_remainder
    u (gradient u) H hR hC hα hH happrox
  have hder : ∀ x ∈ U, HasFDerivAt (gradient u) (H x) x := by
    intro x hx
    exact hasFDerivAt_gradient_of_holder_quadratic_remainder hu hd x (H x) (hH x hx)
      hα hR (fun z hz => happrox x hx z hz.le)
  refine ⟨?_, hder⟩
  have hgc : ContDiffOn ℝ 1 (gradient u) U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact hcont.congr (fun x hx => (hder x hx).fderiv)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hd.differentiableOn, ?_, ?_⟩
  · simp
  · have hf : (fun x => (InnerProductSpace.toDual ℝ (E n)) (gradient u x)) = fderiv ℝ u := by
      funext x
      exact (InnerProductSpace.toDual ℝ (E n)).apply_symm_apply (fderiv ℝ u x)
    rw [← hf]
    exact (InnerProductSpace.toDual ℝ (E n)).toContinuousLinearEquiv.contDiff.comp_contDiffOn hgc

end GaussianTilt.MomentMapRegularity
