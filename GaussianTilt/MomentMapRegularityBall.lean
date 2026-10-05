import GaussianTilt.MomentMapRegularityDualDifferentiability

/-! # Ball-target geometry at source infinity

Finite interior conjugate bounds determine the actual recession slope.
These geometric estimates do not assume boundedness of the conjugate at the
boundary, an a priori Hessian estimate, or a maximum-attainment theorem.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma source_lower_bound_of_inner_conjugate_bound {φ : E n → ℝ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hfinite : ∀ p ∈ Metric.ball (0 : E n) R, BddAbove (conjugateValues φ p))
    (hM : ∀ p, ‖p‖ ≤ r → conjugate φ p ≤ M) (x : E n) :
    r * ‖x‖ - M ≤ φ x := by
  by_cases hx : x = 0
  · subst x
    have hp := hfinite 0 (by simpa using hr.trans hrR)
    have h := conjugate_fenchel_le hp 0
    have hm := hM 0 (by simpa using hr.le)
    simp only [inner_zero_left, norm_zero, mul_zero, zero_sub] at *
    linarith
  have hxpos := norm_pos_iff.mpr hx
  let p := (r / ‖x‖) • x
  have hpn : ‖p‖ = r := by
    simp only [p, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hxpos)]
    field_simp
  have hp : p ∈ Metric.ball 0 R := by simpa [Metric.mem_ball, hpn] using hrR
  have h := conjugate_fenchel_le (hfinite p hp) x
  have hm := hM p hpn.le
  have hi : inner ℝ p x = r * ‖x‖ := by
    rw [show p = (r / ‖x‖) • x from rfl, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  rw [hi] at h
  linarith

/-- The normalized source potential tends to the ball radius at infinity,
using only actual convex supporting planes and finite interior conjugates. -/
theorem source_recession_tendsto_ball {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) {R : ℝ} (hR : 0 < R)
    (hg : ∀ x, ‖gradient φ x‖ ≤ R)
    (hfinite : ∀ p ∈ Metric.ball (0 : E n) R, BddAbove (conjugateValues φ p))
    (hlocal : ∀ r, 0 < r → r < R → ∃ M, ∀ p, ‖p‖ ≤ r → conjugate φ p ≤ M) :
    Tendsto (fun x => φ x / ‖x‖) (cocompact (E n)) (𝓝 R) := by
  have hnorm : Tendsto (fun x : E n => ‖x‖) (cocompact (E n)) atTop := tendsto_norm_cocompact_atTop
  have hinv : Tendsto (fun x : E n => ‖x‖⁻¹) (cocompact (E n)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  have hnpos : ∀ᶠ x : E n in cocompact (E n), 0 < ‖x‖ :=
    hnorm.eventually (eventually_gt_atTop 0)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let r := (max a 0 + R) / 2
    have hr : 0 < r := by dsimp [r]; linarith [le_max_right a 0]
    have hrR : r < R := by dsimp [r]; rcases le_total a 0 with h | h <;> simp [max_eq_right h, max_eq_left h] <;> linarith
    have har : a < r := by dsimp [r]; linarith [le_max_left a 0]
    obtain ⟨M, hM⟩ := hlocal r hr hrR
    have hlim : Tendsto (fun x : E n => r - M / ‖x‖) (cocompact (E n)) (𝓝 r) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
    filter_upwards [hlim.eventually (eventually_gt_nhds har), hnpos] with x hx hxn
    apply hx.trans_le
    apply (le_div_iff₀ hxn).mpr
    have h := source_lower_bound_of_inner_conjugate_bound hr hrR hfinite hM x
    field_simp
    nlinarith
  · intro b hb
    have hlim : Tendsto (fun x : E n => R + φ 0 / ‖x‖) (cocompact (E n)) (𝓝 R) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
    filter_upwards [hlim.eventually (eventually_lt_nhds hb), hnpos] with x hx hxn
    apply lt_of_le_of_lt _ hx
    apply (div_le_iff₀ hxn).mpr
    have h := convex_gradient_support hc (hd x) 0
    simp only [zero_sub, inner_neg_right] at h
    have hi := real_inner_le_norm (gradient φ x) x
    have hg' := mul_le_mul_of_nonneg_right (hg x) (norm_nonneg x)
    field_simp
    nlinarith

def radialGradient (R : ℝ) (x : E n) : E n := (R / ‖x‖) • x

/-- Ball support and the actual recession slope force the gradient to
approach the radial boundary gradient, uniformly outside compact sets. -/
theorem gradient_radial_asymptotic {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) {R : ℝ} (hR : 0 < R)
    (hg : ∀ x, ‖gradient φ x‖ ≤ R)
    (hrec : Tendsto (fun x => φ x / ‖x‖) (cocompact (E n)) (𝓝 R)) :
    Tendsto (fun x => gradient φ x - radialGradient R x) (cocompact (E n)) (𝓝 0) := by
  have hnorm : Tendsto (fun x : E n => ‖x‖) (cocompact (E n)) atTop := tendsto_norm_cocompact_atTop
  have hinv : Tendsto (fun x : E n => ‖x‖⁻¹) (cocompact (E n)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  have hnpos := hnorm.eventually (eventually_gt_atTop 0)
  have hlim : Tendsto (fun x : E n => 2 * R * (R - φ x / ‖x‖ + φ 0 / ‖x‖))
      (cocompact (E n)) (𝓝 0) := by
    convert tendsto_const_nhds.mul
      ((tendsto_const_nhds.sub hrec).add (tendsto_const_nhds.mul hinv)) using 1 <;>
      simp [div_eq_mul_inv]
  have hb : ∀ᶠ x in cocompact (E n),
      ‖gradient φ x - radialGradient R x‖^2 ≤ 2 * R * (R - φ x / ‖x‖ + φ 0 / ‖x‖) := by
    filter_upwards [hnpos] with x hx
    have hrad : ‖radialGradient R x‖ = R := by
      simp only [radialGradient, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hx)]
      field_simp
    have hs := convex_gradient_support hc (hd x) 0
    simp only [zero_sub, inner_neg_right] at hs
    have hi := mul_le_mul_of_nonneg_left (show φ x - φ 0 ≤ inner ℝ (gradient φ x) x by linarith)
      (show 0 ≤ 2 * R / ‖x‖ by positivity)
    have hg2 := sq_le_sq₀ (norm_nonneg _) hR.le |>.mpr (hg x)
    rw [norm_sub_sq_real, hrad]
    simp only [radialGradient, inner_smul_right]
    field_simp at hi ⊢
    nlinarith
  have hsq : Tendsto (fun x => ‖gradient φ x - radialGradient R x‖^2)
      (cocompact (E n)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun x => sq_nonneg _)) hb hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- The recession and radial-gradient asymptotics are obtained from the
actual ball-target moment law, without bounded-boundary-conjugate assumptions. -/
theorem gradient_radial_asymptotic_of_ball_transport {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    {R : ℝ} (hR : 0 < R) (hg : ∀ x, ‖gradient φ x‖ ≤ R)
    (hV : ContinuousOn V (Metric.ball 0 R))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball 0 R).indicator (fun y => Real.exp (-V y)) x))) :
    Tendsto (fun x => gradient φ x - radialGradient R x) (cocompact (E n)) (𝓝 0) := by
  obtain ⟨hfinite, _, hconj, _⟩ := conjugate_regular_on_target hφ hc
    Metric.isOpen_ball (convex_ball (0 : E n) R) hV hmap
  apply gradient_radial_asymptotic hc hd hR hg
  apply source_recession_tendsto_ball hc hd hR hg hfinite
  intro r hr hrR
  have hsub : Metric.closedBall (0 : E n) r ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) r).exists_bound_of_continuousOn
    (hconj.mono hsub)
  refine ⟨M, fun p hp => ?_⟩
  exact (le_abs_self _).trans (hM p (by simpa using hp))

lemma normalized_vector_difference_bound {x y : E n} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  have hxn := norm_pos_iff.mpr hx
  have hyn := norm_pos_iff.mpr hy
  have he : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by module
  have hs : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    rw [show ‖x‖⁻¹ - ‖y‖⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) by field_simp]
    rw [abs_div, abs_mul, abs_of_pos hxn, abs_of_pos hyn]
    field_simp
  calc
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := he ▸ norm_add_le _ _
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hxn), hs]
      ring
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by
      gcongr
      simpa [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = _ := by ring

lemma radialGradient_translation_tendsto_zero (R : ℝ) (h : E n) :
    Tendsto (fun x => radialGradient R (x + h) - radialGradient R x)
      (cocompact (E n)) (𝓝 0) := by
  have hnorm : Tendsto (fun x : E n => ‖x‖) (cocompact (E n)) atTop := tendsto_norm_cocompact_atTop
  have hinv : Tendsto (fun x : E n => ‖x‖⁻¹) (cocompact (E n)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  have hlim : Tendsto (fun x : E n => |R| * (2 * ‖h‖ / ‖x‖))
      (cocompact (E n)) (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_const_nhds.mul hinv)
  have hb : ∀ᶠ x in cocompact (E n),
      ‖radialGradient R (x + h) - radialGradient R x‖ ≤ |R| * (2 * ‖h‖ / ‖x‖) := by
    filter_upwards [hnorm.eventually (eventually_gt_atTop (‖h‖ + 1))] with x hx
    have hxn : x ≠ 0 := by intro hz; simp [hz] at hx; linarith [norm_nonneg h]
    have hxh : x + h ≠ 0 := by
      intro hz
      have he : x = -h := eq_neg_of_add_eq_zero_left hz
      rw [he, norm_neg] at hx
      linarith
    have hbd := normalized_vector_difference_bound hxn hxh
    have he : radialGradient R (x + h) - radialGradient R x =
        R • (‖x + h‖⁻¹ • (x + h) - ‖x‖⁻¹ • x) := by
      dsimp [radialGradient]
      simp [div_eq_mul_inv, smul_sub, smul_smul]
    rw [he, norm_smul, Real.norm_eq_abs, norm_sub_rev]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg R)
    simpa only [show x - (x + h) = -h by abel, norm_neg] using hbd
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _)) hb hlim

/-- The difference of endpoint gradients tends to zero at infinity. For a
ball target this follows from proved recession geometry, with no Hessian
bound and no boundary bound on the dual potential. -/
theorem gradient_translation_gap_of_radial_asymptotic {φ : E n → ℝ} {R : ℝ}
    (hasym : Tendsto (fun x => gradient φ x - radialGradient R x)
      (cocompact (E n)) (𝓝 0)) (h : E n) :
    Tendsto (fun x => gradient φ (x + h) - gradient φ (x + -h))
      (cocompact (E n)) (𝓝 0) := by
  have hp := hasym.comp (Homeomorph.addRight h).isClosedEmbedding.tendsto_cocompact
  have hm := hasym.comp (Homeomorph.addRight (-h)).isClosedEmbedding.tendsto_cocompact
  have hr := (radialGradient_translation_tendsto_zero R h).sub
    (radialGradient_translation_tendsto_zero R (-h))
  have hh := (hp.sub hm).add hr
  convert hh using 1
  · funext x
    simp only [Function.comp_apply]
    change gradient φ (x + h) - gradient φ (x + -h) =
      ((gradient φ (x + h) - radialGradient R (x + h)) -
      (gradient φ (x + -h) - radialGradient R (x + -h))) +
      ((radialGradient R (x + h) - radialGradient R x) -
      (radialGradient R (x + -h) - radialGradient R x))
    abel
  · simp

end GaussianTilt.MomentMapRegularity
