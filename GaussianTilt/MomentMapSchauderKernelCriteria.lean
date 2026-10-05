import GaussianTilt.MomentMapSchauderSingularHolder

/-!
# Discharging singular-integral hypotheses from actual kernel data

A compactly supported measurable kernel with the usual size and actual
Fréchet derivative decay automatically has the integrability and
separated-point smoothness needed in the proved Hölder theorem.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped ENNReal Topology
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The genuine derivative decay implies the separated-point kernel
estimate by the ordinary mean-value inequality on a ball away from zero. -/
theorem kernel_difference_of_derivative_decay {K : E → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hdiff : ∀ z ≠ 0, DifferentiableAt ℝ K z)
    (hderiv : ∀ z ≠ 0, ‖fderiv ℝ K z‖ ≤ D * ‖z‖ ^ (-(finrank ℝ E : ℝ) - 1))
    (a b : E) (ha : a ≠ 0) (hab : ‖a - b‖ ≤ ‖a‖ / 2) :
    |K a - K b| ≤ (D * (2 : ℝ) ^ ((finrank ℝ E : ℝ) + 1)) *
      ‖a - b‖ * ‖a‖ ^ (-(finrank ℝ E : ℝ) - 1) := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hn (z : E) (hz : z ∈ Metric.closedBall a (‖a‖ / 2)) : ‖a‖ / 2 ≤ ‖z‖ := by
    have hz' : ‖a - z‖ ≤ ‖a‖ / 2 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
    have htri := norm_sub_le_norm_sub_add_norm_sub a z (0 : E)
    simp only [sub_zero] at htri
    linarith
  have hzne (z : E) (hz : z ∈ Metric.closedBall a (‖a‖ / 2)) : z ≠ 0 :=
    norm_pos_iff.mp ((half_pos hna).trans_le (hn z hz))
  have hbound : ∀ z ∈ Metric.closedBall a (‖a‖ / 2),
      ‖fderiv ℝ K z‖ ≤ D * (‖a‖ / 2) ^ (-(finrank ℝ E : ℝ) - 1) := by
    intro z hz
    exact (hderiv z (hzne z hz)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (half_pos hna) (hn z hz) (by linarith [show (0 : ℝ) ≤ (finrank ℝ E : ℝ) from Nat.cast_nonneg _])) hD)
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => hdiff z (hzne z hz)) hbound (convex_closedBall a (‖a‖ / 2))
    (show a ∈ Metric.closedBall a (‖a‖ / 2) by simpa using (half_pos hna).le)
    (show b ∈ Metric.closedBall a (‖a‖ / 2) by
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hab)
  have he : (‖a‖ / 2) ^ (-(finrank ℝ E : ℝ) - 1) =
      (2 : ℝ) ^ ((finrank ℝ E : ℝ) + 1) * ‖a‖ ^ (-(finrank ℝ E : ℝ) - 1) := by
    rw [Real.div_rpow (norm_nonneg a) (by norm_num)]
    have hexp : -(finrank ℝ E : ℝ) - 1 = -((finrank ℝ E : ℝ) + 1) := by ring
    rw [hexp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  rw [he] at hb
  simpa only [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using hb

/-- The compensated integrand is globally integrable once the actual kernel
vanishes outside a finite ball. -/
theorem compensated_kernel_integrable_of_support_bound {K f : E → ℝ} {M H α R : ℝ}
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hα : 0 < α) (hαn : α < (finrank ℝ E : ℝ)) (hR : 0 < R)
    (hKm : Measurable K) (hfm : Measurable f)
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hsupp : ∀ z, R < ‖z‖ → K z = 0)
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (x : E) :
    Integrable (fun z => K (x - z) * (f z - f x)) μ := by
  have hi := integrableOn_compensated_kernel_closedBall (μ := μ) hM hH hα hαn hKm hfm hK hf x hR
  have hii := (integrable_indicator_iff measurableSet_closedBall).mpr hi
  have he : (Metric.closedBall x R).indicator (fun z => K (x - z) * (f z - f x)) =
      (fun z => K (x - z) * (f z - f x)) := by
    funext z
    by_cases hz : z ∈ Metric.closedBall x R
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz]
      have hz' : R < ‖x - z‖ := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] using hz
      rw [hsupp (x - z) hz', zero_mul]
  rwa [he] at hii

/-- Actual tail integrability follows from the size bound and finite kernel
support, independently of any cancellation identity. -/
theorem kernel_tail_integrable_of_support_bound {K : E → ℝ} {M R : ℝ}
    (hM : 0 ≤ M) (hKm : Measurable K)
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hsupp : ∀ z, R < ‖z‖ → K z = 0) {r : ℝ} (hr : 0 < r) :
    IntegrableOn K (Metric.closedBall (0 : E) r)ᶜ μ := by
  let g : E → ℝ := (Metric.closedBall (0 : E) r)ᶜ.indicator K
  have hg : Measurable g := hKm.indicator measurableSet_closedBall.compl
  have hb : ∀ z : E, ‖g z‖ ≤ M * r ^ (-(finrank ℝ E : ℝ)) := by
    intro z
    by_cases hz : z ∈ (Metric.closedBall (0 : E) r)ᶜ
    · have hz' : r < ‖z‖ := by simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hz
      have hn : 0 < ‖z‖ := hr.trans hz'
      simp only [g, indicator_of_mem hz, Real.norm_eq_abs]
      exact (hK z (norm_pos_iff.mp hn)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hr hz'.le (neg_nonpos.mpr (Nat.cast_nonneg _))) hM)
    · simp only [g, indicator_of_notMem hz, norm_zero]
      positivity
  have hi : IntegrableOn g (Metric.closedBall (0 : E) R) μ := by
    apply (integrableOn_const (C := M * r ^ (-(finrank ℝ E : ℝ))) measure_closedBall_lt_top.ne).mono'
      hg.aestronglyMeasurable
    exact Eventually.of_forall hb
  have hii := (integrable_indicator_iff measurableSet_closedBall).mpr hi
  have he : (Metric.closedBall (0 : E) R).indicator g = g := by
    funext z
    by_cases hz : z ∈ Metric.closedBall (0 : E) R
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz]
      have hz' : R < ‖z‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
      dsimp [g]
      by_cases hz2 : z ∈ (Metric.closedBall (0 : E) r)ᶜ
      · rw [indicator_of_mem hz2, hsupp z hz']
      · rw [indicator_of_notMem hz2]
  rw [he] at hii
  exact (integrable_indicator_iff measurableSet_closedBall.compl).mp hii

/-- The Hölder estimate with all integrability and finite-increment
smoothness discharged from actual compact kernel support and derivatives. -/
theorem compensatedSingularIntegral_holder_of_kernel_derivative
    {K f : E → ℝ} {M D H α R : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hα : 0 < α) (hα1 : α < 1) (hαn : α < (finrank ℝ E : ℝ)) (hR : 0 < R)
    (hKm : Measurable K) (hfm : Measurable f)
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hdiff : ∀ z ≠ 0, DifferentiableAt ℝ K z)
    (hderiv : ∀ z ≠ 0, ‖fderiv ℝ K z‖ ≤ D * ‖z‖ ^ (-(finrank ℝ E : ℝ) - 1))
    (hsupp : ∀ z, R < ‖z‖ → K z = 0)
    (hcancel : ∀ r : ℝ, 0 < r → ∫ z in (Metric.closedBall (0 : E) r)ᶜ, K z ∂μ = 0)
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (x y : E) :
    |compensatedSingularIntegral μ K f x - compensatedSingularIntegral μ K f y| ≤
      singularHolderConstant μ M (D * (2 : ℝ) ^ ((finrank ℝ E : ℝ) + 1)) α *
        H * ‖x - y‖ ^ α := by
  apply compensatedSingularIntegral_holder_bound hM (by positivity) hH hα hα1 hαn hK
    (kernel_difference_of_derivative_decay hD hdiff hderiv) hf
  · exact compensated_kernel_integrable_of_support_bound hM hH hα hαn hR hKm hfm hK hsupp hf
  · intro r hr
    exact kernel_tail_integrable_of_support_bound hM hKm hK hsupp hr
  · exact hcancel

lemma singularHolderConstant_nonneg {M L α : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) :
    0 ≤ singularHolderConstant μ M L α := by
  have hi : 0 ≤ ∫ z in Metric.closedBall (0 : E) 1,
      ‖z‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ :=
    integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg z) _)
  have hj : 0 ≤ ∫ z in (Metric.closedBall (0 : E) 1)ᶜ,
      ‖z‖ ^ (α - (finrank ℝ E : ℝ) - 1) ∂μ :=
    integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg z) _)
  dsimp [singularHolderConstant]
  positivity

end GaussianTilt.MomentMapSchauder
