import GaussianTilt.MomentMapLinearDirichletHarmonicMollification

/-! # Actual compact Hölder-preserving smooth approximation of Poisson data -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma harmonicMollify_holder {f : KernelSpace n → ℝ} (hf : Continuous f) {H α : ℝ}
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (k : ℕ) (x y : KernelSpace n) :
    |harmonicMollify k f x - harmonicMollify k f y| ≤ H * ‖x - y‖ ^ α := by
  let ρ := (harmonicMollifierBump n k).normed (volume : Measure (KernelSpace n))
  have hi (z : KernelSpace n) : Integrable (fun t => ρ t * f (z - t)) volume :=
    (harmonicMollifierBump n k).hasCompactSupport_normed.convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (harmonicMollifierBump n k).continuous_normed hf.locallyIntegrable z
  have he : harmonicMollify k f x - harmonicMollify k f y =
      ∫ t, ρ t * (f (x - t) - f (y - t)) := by
    simp only [harmonicMollify, harmonicConvolution, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [← integral_sub (hi x) (hi y)]
    congr 1
    funext t
    ring
  rw [he, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le
    ((harmonicMollifierBump n k).integrable_normed.mul_const (H * ‖x - y‖ ^ α))
    (ae_of_all volume (fun t => show ‖ρ t * (f (x - t) - f (y - t))‖ ≤ ρ t * (H * ‖x - y‖ ^ α) by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((harmonicMollifierBump n k).nonneg_normed t)]
      apply mul_le_mul_of_nonneg_left _ ((harmonicMollifierBump n k).nonneg_normed t)
      simpa only [sub_sub_sub_cancel_right] using hholder (x - t) (y - t)))
  simpa only [ρ, integral_mul_const, ContDiffBump.integral_normed, one_mul] using hb

lemma harmonicMollify_tendsto_of_continuous {f : KernelSpace n → ℝ} (hf : Continuous f) (x : KernelSpace n) :
    Tendsto (fun k => harmonicMollify k f x) atTop (𝓝 (f x)) := by
  apply ContDiffBump.convolution_tendsto_right_of_continuous (φ := harmonicMollifierBump n) _ hf x
  change Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma harmonicMollify_support_bound {f : KernelSpace n → ℝ} {A : ℝ}
    (hf : Function.support f ⊆ Metric.closedBall 0 A) (k : ℕ) :
    Function.support (harmonicMollify k f) ⊆ Metric.closedBall 0 (A + 1) := by
  intro x hx
  have hs := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)
    (f := (harmonicMollifierBump n k).normed (volume : Measure (KernelSpace n))) (g := f) (μ := volume) hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hs
  rw [(harmonicMollifierBump n k).support_normed_eq] at hy
  have hy' : ‖y‖ < ((k : ℝ) + 1)⁻¹ := by simpa only [Metric.mem_ball, dist_zero_right, harmonicMollifierBump] using hy
  have hrad : ((k : ℝ) + 1)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    norm_cast; omega
  have hz' : ‖z‖ ≤ A := by simpa only [Metric.mem_closedBall, dist_zero_right] using hf hz
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (norm_add_le _ _).trans (by linarith)

end GaussianTilt.MomentMapLinearDirichlet
