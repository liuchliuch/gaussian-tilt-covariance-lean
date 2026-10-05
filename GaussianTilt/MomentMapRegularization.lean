import GaussianTilt.MomentMapGaussianApproximation
import GaussianTilt.BlockPrekopa
import GaussianTilt.LogConcavity

/-!
# Actual smooth convolution densities for moment-map regularization

For an integrable compactly supported input, convolution with an everywhere
smooth kernel is smooth. The proof localizes the kernel with a constructed
smooth bump, then applies the proved compact-kernel convolution theorem. No
global derivative bounds for the kernel and no differentiability-under-the-
integral premise are needed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators Convolution ContDiff
namespace GaussianTilt.MomentMapApproximation
open Paouris LogConcaveMarginal

variable {n : ℕ}

/-- Smoothness of convolution when the integrable input, rather than the
smooth kernel, has compact support. -/
theorem contDiff_convolution_of_bounded_support {f g : Reference.Space n → ℝ}
    (hf : Integrable f) (hg : ContDiff ℝ ∞ g) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, R < ‖y‖ → f y = 0) : ContDiff ℝ ∞ (f ⋆ g) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  let b : ContDiffBump (0 : Reference.Space n) :=
    ⟨‖x₀‖ + R + 2, ‖x₀‖ + R + 3, by positivity, by linarith⟩
  let g' : Reference.Space n → ℝ := fun y => b y * g y
  have hg' : ContDiff ℝ ∞ g' := b.contDiff.mul hg
  have hgs : HasCompactSupport g' := b.hasCompactSupport.mul_right
  have hconv : ContDiff ℝ ∞ (f ⋆ g') :=
    hgs.contDiff_convolution_right _ hf.locallyIntegrable hg'
  apply hconv.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
  change (∫ y, f y * g (x - y)) = ∫ y, f y * g' (x - y)
  apply integral_congr_ae
  apply ae_of_all
  intro y
  by_cases hy : R < ‖y‖
  · simp [hs y hy]
  · have hyR : ‖y‖ ≤ R := le_of_not_gt hy
    have hxx : ‖x - x₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hxnorm : ‖x‖ < 1 + ‖x₀‖ := by
      calc
        ‖x‖ = ‖(x - x₀) + x₀‖ := by congr 1; abel
        _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
        _ < _ := add_lt_add_right hxx _
    have hb : b (x - y) = 1 := b.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      change ‖x - y‖ ≤ ‖x₀‖ + R + 2
      have hn := norm_sub_le x y
      linarith)
    simp [g', hb]

lemma standardGaussianDensity_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (standardGaussianDensity n) := by
  unfold standardGaussianDensity gaussianKernel
  have hn : ContDiff ℝ ∞ (fun x : Reference.Space n => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  exact (contDiff_const.mul hn).exp.div_const _

lemma standardGaussianDensity_logconcave (n : ℕ) :
    IsLogConcave (standardGaussianDensity n) := by
  have hbase := Reference.gaussian_logconcaveDensity (n := n)
    (1 / 2) (Real.log (∫ y, gaussianKernel n y)) (by norm_num)
  have he : standardGaussianDensity n =
      fun x => Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2 - Real.log (∫ y, gaussianKernel n y)) := by
    funext x
    rw [Real.exp_sub, Real.exp_log (gaussianKernel_integral_pos n)]
    rfl
  rw [he]
  exact ⟨hbase.1, hbase.2.2⟩

/-- A Gaussian convolution is genuinely smooth for compact input density. -/
theorem gaussianConvolution_contDiff {f : Reference.Space n → ℝ}
    (hf : Integrable f) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, R < ‖y‖ → f y = 0) :
    ContDiff ℝ ∞ (f ⋆ standardGaussianDensity n) :=
  contDiff_convolution_of_bounded_support hf (standardGaussianDensity_contDiff n) hR hs

/-- Prékopa proves logconcavity of the actual convolution. The integration
block is converted to product coordinates by a volume-preserving linear
equivalence, rather than taking convolution preservation as an assumption. -/
theorem convolution_logconcave_of_bounded_support {f g : Reference.Space n → ℝ}
    (hf : IsLogConcave f) (hg : IsLogConcave g) (hfm : Measurable f) (hgm : Measurable g)
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) : IsLogConcave (f ⋆ g) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  let L₁ : (Reference.Space n × (Fin n → ℝ)) →ₗ[ℝ] Reference.Space n :=
    e.toLinearMap.comp (LinearMap.snd ℝ _ _)
  let L₂ : (Reference.Space n × (Fin n → ℝ)) →ₗ[ℝ] Reference.Space n :=
    LinearMap.fst ℝ _ _ - L₁
  let F : Reference.Space n × (Fin n → ℝ) → ℝ := fun p => f (L₁ p) * g (L₂ p)
  have hF : IsLogConcave F :=
    (BlockPrekopa.logconcave_comp_linear hf L₁).mul (BlockPrekopa.logconcave_comp_linear hg L₂)
  have hFm : Measurable F :=
    (hfm.comp L₁.continuous_of_finiteDimensional.measurable).mul
      (hgm.comp L₂.continuous_of_finiteDimensional.measurable)
  have hFs (x : Reference.Space n) (y : Fin n → ℝ) (hy : R < ‖y‖) : F (x, y) = 0 := by
    have hnorm : ‖y‖ ≤ ‖e y‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg (e y))).mpr
      intro i
      exact PiLp.norm_apply_le (e y) i
    change f (e y) * g (x - e y) = 0
    rw [hs _ (hy.trans_le hnorm), zero_mul]
  have h := (BlockPrekopa.logconcave_marginal_and_fibres hF hFm hFs).1
  have heq : (fun x => ∫ y : Fin n → ℝ, F (x, y)) = f ⋆ g := by
    funext x
    change (∫ y : Fin n → ℝ, f (WithLp.toLp 2 y) * g (x - WithLp.toLp 2 y)) =
      ∫ y : Reference.Space n, f y * g (x - y)
    exact (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      (EuclideanSpace.measurableEquiv (Fin n)).symm.measurableEmbedding
      (fun y : Reference.Space n => f y * g (x - y))
  rw [heq] at h
  exact h

theorem gaussianConvolution_logconcave {f : Reference.Space n → ℝ}
    (hf : IsLogConcave f) (hfm : Measurable f)
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) :
    IsLogConcave (f ⋆ standardGaussianDensity n) :=
  convolution_logconcave_of_bounded_support hf (standardGaussianDensity_logconcave n)
    hfm (standardGaussianDensity_continuous n).measurable hs

lemma hasCompactSupport_of_bounded_support {f : Reference.Space n → ℝ}
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) : HasCompactSupport f := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Reference.Space n) R)
  intro y hy
  apply hs
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy

/-- Positive convolution kernels give strictly positive density everywhere. -/
theorem convolution_pos_of_positive_right {f g : Reference.Space n → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f) (hfmass : 0 < ∫ x, f x)
    (hg : ∀ x, 0 < g x) (hgc : Continuous g)
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) (x : Reference.Space n) :
    0 < (f ⋆ g) x := by
  have hi : Integrable (fun y => f y * g (x - y)) :=
    (hasCompactSupport_of_bounded_support hs).convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hfi.locallyIntegrable hgc x
  apply (integral_pos_iff_support_of_nonneg
    (fun y => mul_nonneg (hf y) (hg _).le) hi).mpr
  have heq : Function.support (fun y => f y * g (x - y)) =
      Function.support f := by
    ext y
    simp only [Function.mem_support, ne_eq, mul_eq_zero,
      (hg (x - y)).ne', or_false]
  rw [heq]
  exact (integral_pos_iff_support_of_nonneg hf hfi).mp hfmass

/-- Everywhere positivity of the smoothed density follows from the actual
positive mass of the input and strict positivity of the Gaussian kernel. -/
theorem gaussianConvolution_pos {f : Reference.Space n → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f) (hfmass : 0 < ∫ x, f x)
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) (x : Reference.Space n) :
    0 < (f ⋆ standardGaussianDensity n) x :=
  convolution_pos_of_positive_right hf hfi hfmass standardGaussianDensity_pos
    (standardGaussianDensity_continuous n) hs x

/-- The actual positive Gaussian convolution has a finite, smooth, convex
negative-log potential on the whole space. -/
theorem gaussianConvolution_potential {f : Reference.Space n → ℝ}
    (hf : IsLogConcave f) (hfm : Measurable f) (hfi : Integrable f)
    (hfmass : 0 < ∫ x, f x) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, R < ‖y‖ → f y = 0) :
    let V := fun x => -Real.log ((f ⋆ standardGaussianDensity n) x)
    ContDiff ℝ ∞ V ∧ ConvexOn ℝ univ V ∧
      ∀ x, Real.exp (-V x) = (f ⋆ standardGaussianDensity n) x := by
  dsimp only
  have hp := gaussianConvolution_pos hf.1 hfi hfmass hs
  refine ⟨((gaussianConvolution_contDiff hfi hR hs).log (fun x => (hp x).ne')).neg,
    convexOn_neg_log (gaussianConvolution_logconcave hf hfm hs) (convex_univ) (fun x _ => hp x), ?_⟩
  intro x
  simp only [neg_neg, Real.exp_log (hp x)]

end GaussianTilt.MomentMapApproximation
