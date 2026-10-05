import GaussianTilt.MomentMapSchauderSingularIntegral

/-!
# The displaced cancellation error in a singular-integral Hölder estimate

Cancellation of true tail integrals reduces the displaced far-field integral
to a shell with fixed radius ratio. Its size is bounded by actual Haar ball
volume, independent of the distance between the two evaluation points.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped ENNReal Topology
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma outside_doubleBall_subset_outside_displacedBall (x y : E) :
    (Metric.closedBall x (2 * ‖x - y‖))ᶜ ⊆ (Metric.closedBall y ‖x - y‖)ᶜ := by
  intro z hz
  have hz' : 2 * ‖x - y‖ < ‖x - z‖ := by
    simpa only [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] using hz
  have ht := norm_sub_le_norm_sub_add_norm_sub x y z
  have hzy : ‖x - y‖ < ‖y - z‖ := by linarith
  simpa only [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] using hzy

/-- Actual tail cancellation bounds the displaced tail integral by a
radius-independent constant. This is the cancellation term needed to remove
the spurious logarithm in a naive Hölder estimate. -/
theorem displaced_kernel_tail_bound {K : E → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hint : ∀ r : ℝ, 0 < r → IntegrableOn K (Metric.closedBall (0 : E) r)ᶜ μ)
    (hcancel : ∀ r : ℝ, 0 < r → ∫ z in (Metric.closedBall (0 : E) r)ᶜ, K z ∂μ = 0)
    {x y : E} (hxy : x ≠ y) :
    |∫ z in (Metric.closedBall x (2 * ‖x - y‖))ᶜ, K (y - z) ∂μ| ≤
      M * (2 : ℝ) ^ finrank ℝ E * μ.real (Metric.ball (0 : E) 1) := by
  let d : ℝ := ‖x - y‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let S : Set E := Metric.closedBall x (2 * d)
  let T : Set E := (Metric.closedBall y d)ᶜ
  let D : Set E := T \ Sᶜ
  have hsub : Sᶜ ⊆ T := outside_doubleBall_subset_outside_displacedBall x y
  have hD : D ⊆ S := by
    intro z hz
    exact not_not.mp hz.2
  have hDT : D ⊆ T := diff_subset
  have hiT : IntegrableOn (fun z => K (y - z)) T μ :=
    (integrableOn_center_sub_outside_closedBall_iff (μ := μ) K y d).mpr (hint d hd)
  have hc : (∫ z in T, K (y - z) ∂μ) = 0 := by
    rw [integral_center_sub_outside_closedBall K y d]
    exact hcancel d hd
  have hid := integral_diff (s := T) (t := Sᶜ) measurableSet_closedBall.compl hiT hsub
  rw [hc, zero_sub] at hid
  have hconst : IntegrableOn (fun _ : E => M * d ^ (-(finrank ℝ E : ℝ))) S μ :=
    integrableOn_const measure_closedBall_lt_top.ne
  have hb := norm_integral_le_of_norm_le
    (f := fun z => K (y - z)) (IntegrableOn.mono_set hconst hD) ?_
  · have hmono := setIntegral_mono_set hconst
      (Eventually.of_forall (fun _ => by positivity)) (Eventually.of_forall hD)
    have hb' := hb.trans hmono
    change ‖∫ z in D, K (y - z) ∂μ‖ ≤ _ at hb'
    rw [show (∫ z in D, K (y - z) ∂μ) = -(∫ z in Sᶜ, K (y - z) ∂μ) from hid,
      norm_neg, Real.norm_eq_abs, setIntegral_const, smul_eq_mul] at hb'
    apply hb'.trans_eq
    dsimp only [S]
    rw [measureReal_def, μ.addHaar_closedBall x (by positivity : 0 ≤ 2 * d),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by positivity) _),
      Real.rpow_neg hd.le, Real.rpow_natCast]
    change (2 * d) ^ finrank ℝ E * (μ (Metric.ball (0 : E) 1)).toReal *
      (M * (d ^ finrank ℝ E)⁻¹) = _
    rw [mul_pow]
    dsimp only [measureReal_def]
    have hdN : d ^ finrank ℝ E ≠ 0 := pow_ne_zero _ hd.ne'
    field_simp
  · filter_upwards [ae_restrict_mem
      (measurableSet_closedBall.compl.diff measurableSet_closedBall.compl)] with z hz
    have hzT := hDT hz
    have hnorm : d < ‖y - z‖ := by
      simpa only [T, mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] using hzT
    have hn : 0 < ‖y - z‖ := hd.trans hnorm
    have hp : ‖y - z‖ ^ (-(finrank ℝ E : ℝ)) ≤ d ^ (-(finrank ℝ E : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hd hnorm.le (neg_nonpos.mpr (Nat.cast_nonneg _))
    simpa only [Real.norm_eq_abs] using (hK (y - z) (norm_pos_iff.mp hn)).trans
      (mul_le_mul_of_nonneg_left hp hM)

end GaussianTilt.MomentMapSchauder
