import GaussianTilt.MomentMapRegularitySecondOrderInterpolation

/-! # Genuine differentiation of convex quadratic expansions

Quadratic approximation is not itself a classical Hessian premise. The
supporting-slope interpolation estimate proves that a quadratic Peano
expansion of a differentiable convex function differentiates its actual
gradient. This is the analytic endpoint of the Campanato jet construction.
-/
noncomputable section
open Set Filter Asymptotics
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def quadraticJet (a : ℝ) (p x : E n) (H : E n →L[ℝ] E n) (y : E n) : ℝ :=
  a + inner ℝ p (y - x) + (1 / 2 : ℝ) * inner ℝ (H (y - x)) (y - x)

lemma quadraticJet_remainder (a : ℝ) (p x y z : E n) (H : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w)) :
    quadraticJet a p x H z - quadraticJet a p x H y -
      inner ℝ (p + H (y - x)) (z - y) =
        (1 / 2 : ℝ) * inner ℝ (H (z - y)) (z - y) := by
  have hz : z - x = (z - y) + (y - x) := by abel
  simp only [quadraticJet, hz, map_add, inner_add_left, inner_add_right]
  rw [hH (z - y) (y - x), real_inner_comm (z - y) (H (y - x))]
  ring

lemma quadraticJet_remainder_le (a : ℝ) (p x y z : E n) (H : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w)) {r : ℝ}
    (hr : 0 ≤ r) (hz : z ∈ Metric.closedBall y r) :
    quadraticJet a p x H z - quadraticJet a p x H y -
      inner ℝ (p + H (y - x)) (z - y) ≤ ‖H‖ * r ^ 2 := by
  rw [quadraticJet_remainder a p x y z H hH]
  have hd : ‖z - y‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hi := real_inner_le_norm (H (z - y)) (z - y)
  have hN := H.le_opNorm (z - y)
  have hmul := mul_le_mul_of_nonneg_right hN (norm_nonneg (z - y))
  have hsq : ‖z - y‖ ^ 2 ≤ r ^ 2 := sq_le_sq₀ (norm_nonneg _) hr |>.mpr hd
  have hn : 0 ≤ ‖H‖ * r ^ 2 := mul_nonneg (norm_nonneg H) (sq_nonneg r)
  nlinarith [mul_le_mul_of_nonneg_left hsq (norm_nonneg H)]

/-- A convex potential's true gradient is differentiable at every point
where a symmetric quadratic Peano expansion exists. -/
theorem hasFDerivAt_gradient_of_quadratic_peano
    {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    (x : E n) (H : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : E n, ‖z - x‖ < δ →
      |u z - quadraticJet (u x) (gradient u x) x H z| ≤ ε * ‖z - x‖ ^ 2) :
    HasFDerivAt (gradient u) H x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  let η : ℝ := min 1 (ε / (4 * (‖H‖ + 1)))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηH : ‖H‖ * η ≤ ε / 4 := by
    have ht : η ≤ ε / (4 * (‖H‖ + 1)) := min_le_right _ _
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * (‖H‖ + 1))).mp ht
    nlinarith
  obtain ⟨δ, hδ, happ⟩ := happrox (ε * η / 32) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : E n) (half_pos hδ)] with h hh
  have hhn : ‖h‖ < δ / 2 := by simpa using hh
  by_cases hh0 : h = 0
  · simp [hh0]
  have hr : 0 < ‖h‖ := norm_pos_iff.mpr hh0
  let y := x + h
  let r := η * ‖h‖
  have hrr : 0 < r := mul_pos hη hr
  have he : ∀ z ∈ Metric.closedBall y r,
      |u z - quadraticJet (u x) (gradient u x) x H z| ≤ ε * η / 8 * ‖h‖ ^ 2 := by
    intro z hz
    have hzy : ‖z - y‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hyx : y - x = h := by dsimp [y]; abel
    have hzx : ‖z - x‖ ≤ 2 * ‖h‖ := by
      calc
        ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := norm_sub_le_norm_sub_add_norm_sub z y x
        _ ≤ r + ‖h‖ := by rw [hyx]; exact add_le_add_right hzy _
        _ ≤ 2 * ‖h‖ := by dsimp [r]; nlinarith
    have hsmall : ‖z - x‖ < δ := by linarith
    have ht := happ z hsmall
    have hs : ‖z - x‖ ^ 2 ≤ 4 * ‖h‖ ^ 2 := by nlinarith [norm_nonneg (z - x)]
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ ε * η / 32 by positivity)]
  have hb := supporting_slope_error_of_uniform_approximation hrr
    (show 0 ≤ ε * η / 8 * ‖h‖ ^ 2 by positivity) (norm_nonneg H)
    (fun z _ => convex_gradient_support hu (hd y) z) he
    (fun z hz => quadraticJet_remainder_le (u x) (gradient u x) x y z H hH hrr.le hz)
  have hid : y - x = h := by dsimp [y]; abel
  rw [hid] at hb
  have hcoef : 2 * (ε * η / 8 * ‖h‖ ^ 2) / r = ε / 4 * ‖h‖ := by
    dsimp [r]
    field_simp
    <;> ring
  rw [hcoef] at hb
  have hbound : ‖gradient u (x + h) - gradient u x - H h‖ ≤ ε * ‖h‖ := by
    have heq : gradient u (x + h) - gradient u x - H h =
        gradient u y - (gradient u x + H h) := by dsimp [y]; abel
    rw [heq]
    apply hb.trans
    dsimp [r]
    nlinarith [mul_le_mul_of_nonneg_right hηH hr.le]
  exact hbound

/-- A positive-order Taylor remainder is an actual quadratic Peano
expansion, so its symmetric coefficient is the derivative of the gradient. -/
theorem hasFDerivAt_gradient_of_holder_quadratic_remainder
    {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    (x : E n) (H : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w))
    {α R C : ℝ} (hα : 0 < α) (hR : 0 < R)
    (happrox : ∀ z : E n, ‖z - x‖ < R →
      |u z - quadraticJet (u x) (gradient u x) x H z| ≤ C * ‖z - x‖ ^ (2 + α)) :
    HasFDerivAt (gradient u) H x := by
  apply hasFDerivAt_gradient_of_quadratic_peano hu hd x H hH
  intro ε hε
  have hcont : Continuous (fun z : E n => C * ‖z - x‖ ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      ((continuous_id.sub continuous_const).norm))
  have hev : ∀ᶠ z in 𝓝 x, C * ‖z - x‖ ^ α < ε := by
    have h := hcont.continuousAt.eventually (gt_mem_nhds
      (show C * ‖x - x‖ ^ α < ε by simpa [Real.zero_rpow hα.ne'] using hε))
    exact h
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min δ R, lt_min hδ hR, ?_⟩
  intro z hz
  have hzd : dist z x < δ := by simpa only [dist_eq_norm] using (lt_min_iff.mp hz).1
  have he : C * ‖z - x‖ ^ α ≤ ε := (hnear hzd).le
  have ha := happrox z (lt_min_iff.mp hz).2
  rw [Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) hα.le, Real.rpow_two] at ha
  nlinarith [mul_le_mul_of_nonneg_right he (sq_nonneg ‖z - x‖)]

/-- Continuous quadratic coefficients constructed by an approximation
argument give genuine C² regularity on the open set. -/
theorem contDiffOn_two_of_continuous_quadratic_peano
    {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    {U : Set (E n)} (hU : IsOpen U) (H : E n → E n →L[ℝ] E n)
    (hHcont : ContinuousOn H U)
    (hH : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w))
    (happrox : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : E n, ‖z - x‖ < δ →
      |u z - quadraticJet (u x) (gradient u x) x (H x) z| ≤ ε * ‖z - x‖ ^ 2) :
    ContDiffOn ℝ 2 u U := by
  have hg : ∀ x ∈ U, HasFDerivAt (gradient u) (H x) x :=
    fun x hx => hasFDerivAt_gradient_of_quadratic_peano hu hd x (H x) (hH x hx) (happrox x hx)
  have hgc : ContDiffOn ℝ 1 (gradient u) U := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hg x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact hHcont.congr (fun x hx => (hg x hx).fderiv)
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hd.differentiableOn, ?_, ?_⟩
  · simp
  · have hf : (fun x => (InnerProductSpace.toDual ℝ (E n)) (gradient u x)) = fderiv ℝ u := by
      funext x
      exact (InnerProductSpace.toDual ℝ (E n)).apply_symm_apply (fderiv ℝ u x)
    rw [← hf]
    exact (InnerProductSpace.toDual ℝ (E n)).toContinuousLinearEquiv.contDiff.comp_contDiffOn hgc

/-- The linear coefficient of a genuine higher-order approximation is the
actual gradient; it cannot be chosen independently of the function. -/
theorem quadratic_linear_coefficient_eq_gradient
    {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    (a : ℝ) (p x : E n) (H : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w))
    {α R C : ℝ} (hα : 0 < α) (hR : 0 < R) (hC : 0 ≤ C)
    (happrox : ∀ z : E n, ‖z - x‖ ≤ R →
      |u z - quadraticJet a p x H z| ≤ C * ‖z - x‖ ^ (2 + α)) :
    a = u x ∧ p = gradient u x := by
  have ha : a = u x := by
    have hb := happrox x (by simpa using hR.le)
    simp only [quadraticJet, sub_self, map_zero, inner_zero_right, inner_zero_left,
      add_zero, mul_zero, norm_zero, Real.zero_rpow (by linarith : (2 : ℝ) + α ≠ 0)] at hb
    exact (sub_eq_zero.mp (abs_nonpos_iff.mp hb)).symm
  refine ⟨ha, ?_⟩
  have hb : ∀ r : ℝ, 0 < r → r ≤ R →
      ‖gradient u x - p‖ ≤ 2 * C * r ^ (1 + α) + ‖H‖ * r := by
    intro r hr hrR
    have he : ∀ z ∈ Metric.closedBall x r, |u z - quadraticJet a p x H z| ≤ C * r ^ (2 + α) := by
      intro z hz
      have hzr : ‖z - x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
      exact (happrox z (hzr.trans hrR)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hzr (by linarith)) hC)
    have ht := supporting_slope_error_of_uniform_approximation hr
      (show 0 ≤ C * r ^ (2 + α) by positivity) (norm_nonneg H)
      (fun z _ => convex_gradient_support hu (hd x) z) he
      (fun z hz => quadraticJet_remainder_le a p x x z H hH hr.le hz)
    simp only [sub_self, map_zero, add_zero] at ht
    have heq : 2 * (C * r ^ (2 + α)) / r = 2 * C * r ^ (1 + α) := by
      rw [show (2 : ℝ) + α = 1 + (1 + α) by ring, Real.rpow_add hr, Real.rpow_one]
      field_simp
    rwa [heq] at ht
  have ht : Tendsto (fun r : ℝ => 2 * C * r ^ (1 + α) + ‖H‖ * r) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => 2 * C * r ^ (1 + α) + ‖H‖ * r) :=
      (continuous_const.mul (Real.continuous_rpow_const (by linarith))).add
        (continuous_const.mul continuous_id)
    simpa only [Real.zero_rpow (by linarith : (1 : ℝ) + α ≠ 0), mul_zero, add_zero] using
      (hc.continuousAt (x := 0)).continuousWithinAt.tendsto (s := Ioi (0 : ℝ))
  have hzero : ‖gradient u x - p‖ ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R from nhdsWithin_le_nhds (gt_mem_nhds hR))] with r hr hrR
    exact hb r hr hrR.le
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp hzero)).symm

end GaussianTilt.MomentMapRegularity
