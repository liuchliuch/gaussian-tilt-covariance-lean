import GaussianTilt.MomentMapSchauderKernelCriteria

/-!
# The smooth far-field convolution is locally Lipschitz

A globally bounded first derivative controls a fixed near region. The
actual order-minus-dimension-minus-one derivative decay controls the tail
through the already proved Haar power integrals.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped ENNReal Topology
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def scalarKernelConvolution (μ : Measure E) (K f : E → ℝ) (x : E) : ℝ :=
  ∫ z, K (x - z) * f z ∂μ

def smoothTailLipschitzConstant (μ : Measure E) (N L : ℝ) : ℝ :=
  N * μ.real (Metric.closedBall (0 : E) 2) + L * (2 : ℝ)⁻¹ *
    ∫ z in (Metric.closedBall (0 : E) 1)ᶜ, ‖z‖ ^ (-(finrank ℝ E : ℝ) - 1) ∂μ

lemma kernel_global_lipschitz_of_deriv_bound {K : E → ℝ} {N : ℝ}
    (hdiff : Differentiable ℝ K) (hN : ∀ z, ‖fderiv ℝ K z‖ ≤ N) (a b : E) :
    |K a - K b| ≤ N * ‖a - b‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hdiff z) (fun z _ => hN z) convex_univ (mem_univ b) (mem_univ a)
  simpa only [Real.norm_eq_abs] using h

set_option maxHeartbeats 500000 in
/-- Genuine smooth-tail convolution estimate for displacements at most one.
The constant is independent of the support radius of the data. -/
theorem scalarKernelConvolution_local_lipschitz {K f : E → ℝ} {N L F : ℝ}
    (hN : 0 ≤ N) (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hlip : ∀ a b, |K a - K b| ≤ N * ‖a - b‖)
    (hKdiff : ∀ a b : E, a ≠ 0 → ‖a - b‖ ≤ ‖a‖ / 2 →
      |K a - K b| ≤ L * ‖a - b‖ * ‖a‖ ^ (-(finrank ℝ E : ℝ) - 1))
    (hf : ∀ z, |f z| ≤ F)
    (hcomp : ∀ x, Integrable (fun z => K (x - z) * f z) μ)
    (x y : E) (hxy : ‖x - y‖ ≤ 1) :
    |scalarKernelConvolution μ K f x - scalarKernelConvolution μ K f y| ≤
      smoothTailLipschitzConstant μ N L * F * ‖x - y‖ := by
  let G : E → ℝ := fun z => K (x - z) * f z - K (y - z) * f z
  have hiG : Integrable G μ := (hcomp x).sub (hcomp y)
  have he : ∀ z : E, (x - z) - (y - z) = x - y := by intro z; abel
  have hnear : |∫ z in Metric.closedBall x 2, G z ∂μ| ≤
      (N * F * ‖x - y‖) * μ.real (Metric.closedBall (0 : E) 2) := by
    have hic : IntegrableOn (fun _ : E => N * F * ‖x - y‖) (Metric.closedBall x 2) μ :=
      integrableOn_const measure_closedBall_lt_top.ne
    have hb := norm_integral_le_of_norm_le (f := G) hic ?_
    · rw [setIntegral_const, smul_eq_mul] at hb
      have hv : μ.real (Metric.closedBall x 2) = μ.real (Metric.closedBall (0 : E) 2) := by
        simp only [measureReal_def, μ.addHaar_closedBall _ (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [hv] at hb
      simpa only [Real.norm_eq_abs, mul_comm] using hb
    · filter_upwards with z
      dsimp [G]
      rw [← sub_mul, abs_mul]
      have hk := hlip (x - z) (y - z)
      rw [he] at hk
      exact (mul_le_mul hk (hf z) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hk : (finrank ℝ E : ℝ) < (finrank ℝ E : ℝ) + 1 := by linarith
  have hiex : IntegrableOn (fun z : E => ‖z‖ ^ (-(finrank ℝ E : ℝ) - 1))
      (Metric.closedBall 0 2)ᶜ μ := by
    simpa only [neg_add_rev, neg_add, add_comm] using
      integrableOn_norm_neg_rpow_outside_closedBall (μ := μ) hk (R := 2) (by norm_num)
  have hif := ((integrableOn_center_sub_outside_closedBall_iff (μ := μ)
    (fun z : E => ‖z‖ ^ (-(finrank ℝ E : ℝ) - 1)) x 2).mpr hiex).const_mul (L * F * ‖x - y‖)
  have hfar : |∫ z in (Metric.closedBall x 2)ᶜ, G z ∂μ| ≤
      (L * F * ‖x - y‖) * ((2 : ℝ)⁻¹ *
        ∫ z in (Metric.closedBall (0 : E) 1)ᶜ, ‖z‖ ^ (-(finrank ℝ E : ℝ) - 1) ∂μ) := by
    have hb := norm_integral_le_of_norm_le (f := G) hif ?_
    · rw [integral_const_mul, integral_center_sub_outside_closedBall
        (fun z : E => ‖z‖ ^ (-(finrank ℝ E : ℝ) - 1)) x 2,
        integral_norm_rpow_outside_closedBall_scale _ (by norm_num : (0 : ℝ) < 2)] at hb
      have hexp : (finrank ℝ E : ℝ) + (-(finrank ℝ E : ℝ) - 1) = -1 := by ring
      simpa only [Real.norm_eq_abs, hexp, Real.rpow_neg_one] using hb
    · filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with z hz
      have hz' : (2 : ℝ) < ‖x - z‖ := by
        simpa only [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] using hz
      have hn : 0 < ‖x - z‖ := by linarith
      have hk := hKdiff (x - z) (y - z) (norm_pos_iff.mp hn) (by rw [he]; linarith)
      rw [he] at hk
      dsimp [G]
      rw [← sub_mul, abs_mul]
      exact (mul_le_mul hk (hf z) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hsplit := integral_add_compl (s := Metric.closedBall x 2) measurableSet_closedBall hiG
  change |(∫ z, K (x - z) * f z ∂μ) - (∫ z, K (y - z) * f z ∂μ)| ≤ _
  rw [← integral_sub (hcomp x) (hcomp y)]
  change |∫ z, G z ∂μ| ≤ _
  rw [← hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hnear hfar).trans_eq (by
    dsimp [smoothTailLipschitzConstant]
    ring))

lemma smoothTailLipschitzConstant_nonneg {N L : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L) :
    0 ≤ smoothTailLipschitzConstant μ N L := by
  have hi : 0 ≤ ∫ z in (Metric.closedBall (0 : E) 1)ᶜ,
      ‖z‖ ^ (-(finrank ℝ E : ℝ) - 1) ∂μ :=
    integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg z) _)
  dsimp [smoothTailLipschitzConstant]
  positivity

end GaussianTilt.MomentMapSchauder
