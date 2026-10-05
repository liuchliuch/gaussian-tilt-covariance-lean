import GaussianTilt.MomentMapSchauderRadialTail

/-!
# Measured estimates for compensated singular integrals

The near-field cancellation is expressed by the literal difference
`f z - f x`. All integrability and size bounds are derived from the
proved power-integral estimates.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped ENNReal Topology
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma measurePreserving_center_sub (x : E) : MeasurePreserving (fun z => x - z) μ μ := by
  exact μ.measurePreserving_sub_left x

lemma preimage_center_sub_closedBall (x : E) (R : ℝ) :
    (fun z => x - z) ⁻¹' Metric.closedBall 0 R = Metric.closedBall x R := by
  ext z
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, dist_eq_norm, norm_sub_rev, sub_zero]

lemma integrableOn_center_sub_closedBall_iff (f : E → ℝ) (x : E) (R : ℝ) :
    IntegrableOn (fun z => f (x - z)) (Metric.closedBall x R) μ ↔
      IntegrableOn f (Metric.closedBall 0 R) μ := by
  have hp := (measurePreserving_center_sub (μ := μ) x).restrict_preimage
    (s := Metric.closedBall (0 : E) R) measurableSet_closedBall
  rw [preimage_center_sub_closedBall] at hp
  exact hp.integrable_comp_emb (Homeomorph.subLeft x).measurableEmbedding

lemma integral_center_sub_closedBall (f : E → ℝ) (x : E) (R : ℝ) :
    (∫ z in Metric.closedBall x R, f (x - z) ∂μ) = ∫ z in Metric.closedBall 0 R, f z ∂μ := by
  have hp := (measurePreserving_center_sub (μ := μ) x).restrict_preimage
    (s := Metric.closedBall (0 : E) R) measurableSet_closedBall
  rw [preimage_center_sub_closedBall] at hp
  exact hp.integral_comp (Homeomorph.subLeft x).measurableEmbedding f

lemma integrableOn_center_sub_outside_closedBall_iff (f : E → ℝ) (x : E) (R : ℝ) :
    IntegrableOn (fun z => f (x - z)) (Metric.closedBall x R)ᶜ μ ↔
      IntegrableOn f (Metric.closedBall 0 R)ᶜ μ := by
  have hp := (measurePreserving_center_sub (μ := μ) x).restrict_preimage
    (s := (Metric.closedBall (0 : E) R)ᶜ) measurableSet_closedBall.compl
  rw [preimage_compl, preimage_center_sub_closedBall] at hp
  exact hp.integrable_comp_emb (Homeomorph.subLeft x).measurableEmbedding

lemma integral_center_sub_outside_closedBall (f : E → ℝ) (x : E) (R : ℝ) :
    (∫ z in (Metric.closedBall x R)ᶜ, f (x - z) ∂μ) =
      ∫ z in (Metric.closedBall 0 R)ᶜ, f z ∂μ := by
  have hp := (measurePreserving_center_sub (μ := μ) x).restrict_preimage
    (s := (Metric.closedBall (0 : E) R)ᶜ) measurableSet_closedBall.compl
  rw [preimage_compl, preimage_center_sub_closedBall] at hp
  exact hp.integral_comp (Homeomorph.subLeft x).measurableEmbedding f

/-- Pointwise cancellation turns the order-minus-dimension Hessian kernel
into the integrable order `α-dimension` near-field kernel. -/
lemma compensated_kernel_abs_le {K f : E → ℝ} {M H α : ℝ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hα : 0 < α)
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (x z : E) :
    |K (x - z) * (f z - f x)| ≤ (M * H) * ‖x - z‖ ^ (α - (finrank ℝ E : ℝ)) := by
  by_cases hxz : x = z
  · subst z
    simp only [sub_self, mul_zero, abs_zero, norm_zero]
    positivity
  · have hne : x - z ≠ 0 := sub_ne_zero.mpr hxz
    have hn : 0 < ‖x - z‖ := norm_pos_iff.mpr hne
    rw [abs_mul]
    have hff : |f z - f x| ≤ H * ‖x - z‖ ^ α := by
      simpa only [norm_sub_rev] using hf z x
    calc
      _ ≤ (M * ‖x - z‖ ^ (-(finrank ℝ E : ℝ))) * (H * ‖x - z‖ ^ α) :=
        mul_le_mul (hK _ hne) hff (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [show α - (finrank ℝ E : ℝ) = -(finrank ℝ E : ℝ) + α by ring,
          Real.rpow_add hn]
        ring

/-- Absolute integrability of the literal compensated convolution near its
singularity follows from the proved radial layer-cake estimate. -/
theorem integrableOn_compensated_kernel_closedBall {K f : E → ℝ} {M H α : ℝ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hα : 0 < α) (hαn : α < (finrank ℝ E : ℝ))
    (hKm : Measurable K) (hfm : Measurable f)
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (x : E) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun z => K (x - z) * (f z - f x)) (Metric.closedBall x R) μ := by
  have hi := (integrableOn_center_sub_closedBall_iff (μ := μ)
    (fun z : E => ‖z‖ ^ (α - (finrank ℝ E : ℝ))) x R).mpr
      (holderKernel_integrable_and_scale (μ := μ) hα hαn hR).1
  apply (hi.const_mul (M * H)).mono'
    ((hKm.comp (measurable_const.sub measurable_id)).mul (hfm.sub measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    simpa only [Real.norm_eq_abs] using compensated_kernel_abs_le hM hH hα hK hf x z)

/-- Quantitative near-field integral bound for the true compensated kernel. -/
theorem compensated_kernel_near_bound {K f : E → ℝ} {M H α : ℝ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hα : 0 < α) (hαn : α < (finrank ℝ E : ℝ))
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (x : E) {R : ℝ} (hR : 0 < R) :
    |∫ z in Metric.closedBall x R, K (x - z) * (f z - f x) ∂μ| ≤
      (M * H) * (R ^ α * ∫ z in Metric.closedBall (0 : E) 1,
        ‖z‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ) := by
  have hi := (integrableOn_center_sub_closedBall_iff (μ := μ)
    (fun z : E => ‖z‖ ^ (α - (finrank ℝ E : ℝ))) x R).mpr
      (holderKernel_integrable_and_scale (μ := μ) hα hαn hR).1
  have hb := norm_integral_le_of_norm_le (f := fun z => K (x - z) * (f z - f x)) (hi.const_mul (M * H))
    (Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs] using compensated_kernel_abs_le hM hH hα hK hf x z))
  rw [integral_const_mul, integral_center_sub_closedBall (fun z : E => ‖z‖ ^ (α - (finrank ℝ E : ℝ))) x R,
    (holderKernel_integrable_and_scale (μ := μ) hα hαn hR).2] at hb
  simpa only [Real.norm_eq_abs] using hb

/-- The same near-field estimate holds on any measurable or nonmeasurable
subset of the comparison ball, using monotonicity of the nonnegative radial
majorant. This handles the displaced near region in a Hölder comparison. -/
theorem compensated_kernel_near_subset_bound {K f : E → ℝ} {M H α : ℝ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hα : 0 < α) (hαn : α < (finrank ℝ E : ℝ))
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (x : E)
    {S : Set E} {R : ℝ} (hR : 0 < R) (hS : S ⊆ Metric.closedBall x R) :
    |∫ z in S, K (x - z) * (f z - f x) ∂μ| ≤
      (M * H) * (R ^ α * ∫ z in Metric.closedBall (0 : E) 1,
        ‖z‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ) := by
  have hi := ((integrableOn_center_sub_closedBall_iff (μ := μ)
    (fun z : E => ‖z‖ ^ (α - (finrank ℝ E : ℝ))) x R).mpr
      (holderKernel_integrable_and_scale (μ := μ) hα hαn hR).1).const_mul (M * H)
  have hb := norm_integral_le_of_norm_le (f := fun z => K (x - z) * (f z - f x)) (IntegrableOn.mono_set hi hS)
    (Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs] using compensated_kernel_abs_le hM hH hα hK hf x z))
  have hmono := setIntegral_mono_set hi
    (Eventually.of_forall (fun z => by positivity)) (Eventually.of_forall hS)
  have hout := hb.trans hmono
  rw [integral_const_mul, integral_center_sub_closedBall (fun z : E => ‖z‖ ^ (α - (finrank ℝ E : ℝ))) x R,
    (holderKernel_integrable_and_scale (μ := μ) hα hαn hR).2] at hout
  simpa only [Real.norm_eq_abs] using hout

/-- Far-field kernel smoothness turns the difference into a supercritical
integrable power. The separation condition is explicit. -/
lemma kernel_difference_compensated_abs_le {K f : E → ℝ} {L H α : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hKdiff : ∀ a b : E, a ≠ 0 → ‖a - b‖ ≤ ‖a‖ / 2 →
      |K a - K b| ≤ L * ‖a - b‖ * ‖a‖ ^ (-(finrank ℝ E : ℝ) - 1))
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    {x y z : E} (hsep : 2 * ‖x - y‖ < ‖x - z‖) :
    |(K (x - z) - K (y - z)) * (f z - f x)| ≤
      (L * H * ‖x - y‖) * ‖x - z‖ ^ (α - (finrank ℝ E : ℝ) - 1) := by
  have hn : 0 < ‖x - z‖ := lt_of_le_of_lt (by positivity) hsep
  have he : (x - z) - (y - z) = x - y := by abel
  have hk := hKdiff (x - z) (y - z) (norm_pos_iff.mp hn) (by rw [he]; linarith)
  rw [he] at hk
  have hff : |f z - f x| ≤ H * ‖x - z‖ ^ α := by simpa only [norm_sub_rev] using hf z x
  rw [abs_mul]
  calc
    _ ≤ (L * ‖x - y‖ * ‖x - z‖ ^ (-(finrank ℝ E : ℝ) - 1)) *
        (H * ‖x - z‖ ^ α) := mul_le_mul hk hff (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [show α - (finrank ℝ E : ℝ) - 1 = (-(finrank ℝ E : ℝ) - 1) + α by ring,
        Real.rpow_add hn]
      ring

/-- Quantitative integral of the far-field difference, using the true
supercritical power integral rather than a formal radial ansatz. -/
theorem kernel_difference_far_bound {K f : E → ℝ} {L H α : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hα : α < 1)
    (hKdiff : ∀ a b : E, a ≠ 0 → ‖a - b‖ ≤ ‖a‖ / 2 →
      |K a - K b| ≤ L * ‖a - b‖ * ‖a‖ ^ (-(finrank ℝ E : ℝ) - 1))
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (x y : E) {R : ℝ} (hR : 0 < R) (hsep : 2 * ‖x - y‖ ≤ R) :
    |∫ z in (Metric.closedBall x R)ᶜ, (K (x - z) - K (y - z)) * (f z - f x) ∂μ| ≤
      (L * H * ‖x - y‖) * (R ^ (α - 1) *
        ∫ z in (Metric.closedBall (0 : E) 1)ᶜ, ‖z‖ ^ (α - (finrank ℝ E : ℝ) - 1) ∂μ) := by
  have hk : (finrank ℝ E : ℝ) < (finrank ℝ E : ℝ) + 1 - α := by linarith
  have he : -((finrank ℝ E : ℝ) + 1 - α) = α - (finrank ℝ E : ℝ) - 1 := by ring
  have hirad : IntegrableOn (fun z : E => ‖z‖ ^ (α - (finrank ℝ E : ℝ) - 1))
      (Metric.closedBall 0 R)ᶜ μ := by
    simpa only [he] using integrableOn_norm_neg_rpow_outside_closedBall (μ := μ) hk hR
  have hi := ((integrableOn_center_sub_outside_closedBall_iff (μ := μ)
    (fun z : E => ‖z‖ ^ (α - (finrank ℝ E : ℝ) - 1)) x R).mpr hirad).const_mul (L * H * ‖x - y‖)
  have hb := norm_integral_le_of_norm_le
    (f := fun z => (K (x - z) - K (y - z)) * (f z - f x)) hi ?_
  · rw [integral_const_mul, integral_center_sub_outside_closedBall (fun z : E => ‖z‖ ^ (α - (finrank ℝ E : ℝ) - 1)) x R,
      integral_norm_rpow_outside_closedBall_scale _ hR] at hb
    have hexp : (finrank ℝ E : ℝ) + (α - (finrank ℝ E : ℝ) - 1) = α - 1 := by ring
    simpa only [Real.norm_eq_abs, hexp] using hb
  · filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with z hz
    have hz' : R < ‖x - z‖ := by
      simpa only [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le, norm_sub_rev] using hz
    simpa only [Real.norm_eq_abs] using kernel_difference_compensated_abs_le hL hH hKdiff hf (hsep.trans_lt hz')

end GaussianTilt.MomentMapSchauder
