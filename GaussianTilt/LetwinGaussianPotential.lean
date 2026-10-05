import GaussianTilt.LetwinGaussianStein
import GaussianTilt.MomentMapConvolutionLaw

/-! # Smooth finite convex potentials of genuine coordinate Gaussian convolutions -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ContDiff ENNReal Convolution
namespace GaussianTilt.Letwin
open LogConcaveMarginal

lemma coordinate_convolution_logconcave {n : ℕ} {f g : CoordinateSpace n → ℝ}
    (hf : IsLogConcave f) (hg : IsLogConcave g) (hfm : Measurable f) (hgm : Measurable g)
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) : IsLogConcave (f ⋆ g) := by
  let L₁ : (CoordinateSpace n × CoordinateSpace n) →ₗ[ℝ] CoordinateSpace n := LinearMap.snd ℝ _ _
  let L₂ : (CoordinateSpace n × CoordinateSpace n) →ₗ[ℝ] CoordinateSpace n :=
    LinearMap.fst ℝ _ _ - L₁
  let F := fun p : CoordinateSpace n × CoordinateSpace n => f (L₁ p) * g (L₂ p)
  have hF : IsLogConcave F := (BlockPrekopa.logconcave_comp_linear hf L₁).mul
    (BlockPrekopa.logconcave_comp_linear hg L₂)
  have hFm : Measurable F :=
    (hfm.comp L₁.continuous_of_finiteDimensional.measurable).mul
      (hgm.comp L₂.continuous_of_finiteDimensional.measurable)
  have hFs (x y : CoordinateSpace n) (hy : R < ‖y‖) : F (x,y) = 0 := by
    change f y * g (x-y) = 0
    rw [hs y hy, zero_mul]
  exact (BlockPrekopa.logconcave_marginal_and_fibres hF hFm hFs).1

lemma coordinate_convolution_contDiff {n : ℕ} {f g : CoordinateSpace n → ℝ}
    (hf : Integrable f) (hg : ContDiff ℝ ∞ g) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ y, R < ‖y‖ → f y = 0) : ContDiff ℝ ∞ (f ⋆ g) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  let b : ContDiffBump (0 : CoordinateSpace n) :=
    ⟨‖x₀‖ + R + 2, ‖x₀‖ + R + 3, by positivity, by linarith⟩
  let g' : CoordinateSpace n → ℝ := fun y => b y * g y
  have hg' : ContDiff ℝ ∞ g' := b.contDiff.mul hg
  have hgs : HasCompactSupport g' := b.hasCompactSupport.mul_right
  have hconv : ContDiff ℝ ∞ (f ⋆ g') :=
    hgs.contDiff_convolution_right _ hf.locallyIntegrable hg'
  apply hconv.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
  change (∫ y, f y * g (x - y)) = ∫ y, f y * g' (x - y)
  apply integral_congr_ae
  filter_upwards with y
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

lemma coordinate_hasCompactSupport_of_bounded_support {n : ℕ} {f : CoordinateSpace n → ℝ}
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) : HasCompactSupport f := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : CoordinateSpace n) R)
  intro y hy
  apply hs
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy

lemma coordinate_convolution_pos {n : ℕ} {f g : CoordinateSpace n → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f) (hfmass : 0 < ∫ x, f x)
    (hg : ∀ x, 0 < g x) (hgc : Continuous g)
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) (x : CoordinateSpace n) :
    0 < (f ⋆ g) x := by
  have hi : Integrable (fun y => f y * g (x-y)) :=
    (coordinate_hasCompactSupport_of_bounded_support hs).convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hfi.locallyIntegrable hgc x
  apply (integral_pos_iff_support_of_nonneg (fun y => mul_nonneg (hf y) (hg _).le) hi).mpr
  have heq : Function.support (fun y => f y * g (x-y)) = Function.support f := by
    ext y
    simp only [Function.mem_support, ne_eq, mul_eq_zero, (hg (x-y)).ne', or_false]
  rw [heq]
  exact (integral_pos_iff_support_of_nonneg hf hfi).mp hfmass

theorem coordinateGaussian_scaled_smooth_density {n : ℕ} (r : ℝ) (hr : r ≠ 0) :
    ∃ g : CoordinateSpace n → ℝ, ContDiff ℝ ∞ g ∧ IsLogConcave g ∧
      (∀ x, 0 < g x) ∧
      (coordinateGaussian n).map (fun z => r • z) = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
  let e : Reference.Space n ≃L[ℝ] CoordinateSpace n := (euclideanCoordinates n).trans
    (LinearEquiv.smulOfNeZero ℝ (CoordinateSpace n) r hr).toContinuousLinearEquiv
  obtain ⟨c,hc,hl,hm,hmap⟩ := LinearImageDensity.exists_density_map_linearEquiv
    e volume volume (MomentMapApproximation.standardGaussianDensity_logconcave n)
    (Paouris.standardGaussianDensity_continuous n).measurable
  let g := fun x => c * Paouris.standardGaussianDensity n (e.symm x)
  refine ⟨g, contDiff_const.mul ((MomentMapApproximation.standardGaussianDensity_contDiff n).comp e.symm.contDiff),
    hl, (fun x => mul_pos hc (Paouris.standardGaussianDensity_pos _)), ?_⟩
  rw [coordinateGaussian, Measure.map_map (by fun_prop) (euclideanCoordinates n).continuous.measurable]
  exact hmap

lemma coordinate_convolution_withDensity_eq {n : ℕ} {f g : CoordinateSpace n → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hfm : Measurable f) (hgm : Measurable g)
    (hfi : Integrable f) (hgc : Continuous g)
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))) ∗
      (volume.withDensity (fun x => ENNReal.ofReal (g x))) =
    volume.withDensity (fun x => ENNReal.ofReal ((f ⋆ g) x)) := by
  rw [conv_withDensity_eq_lconvolution hfm.ennreal_ofReal hgm.ennreal_ofReal]
  congr 1
  funext x
  rw [lconvolution_def]
  have hi : Integrable (fun y => f y * g (x-y)) :=
    (coordinate_hasCompactSupport_of_bounded_support hs).convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hfi.locallyIntegrable hgc x
  change (∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (g (-y+x))) =
    ENNReal.ofReal (∫ y, f y * g (x-y))
  simp_rw [show ∀ y : CoordinateSpace n, -y+x=x-y by intro y; abel, ← ENNReal.ofReal_mul (hf _)]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun y => mul_nonneg (hf y) (hg (x-y)))).symm

lemma map_add_scaled_eq_convolution {n : ℕ} (μ ν : Measure (CoordinateSpace n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (r : ℝ) :
    (μ.prod ν).map (fun p => p.1 + r • p.2) = μ ∗ (ν.map (fun z => r • z)) := by
  rw [Measure.conv]
  have hprod := Measure.map_prod_map μ ν measurable_id
    (show Measurable (fun z : CoordinateSpace n => r • z) by fun_prop)
  simp only [Measure.map_id] at hprod
  rw [hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Gaussian convolution has a genuinely constructed globally smooth finite
convex potential on coordinate space. No smooth approximation hypothesis is
included in the conclusion's premises. -/
theorem exists_smooth_convex_potential_coordinateGaussian_convolution {n : ℕ}
    {μ : Measure (CoordinateSpace n)} [IsProbabilityMeasure μ]
    {f : CoordinateSpace n → ℝ} (hf : IsLogConcave f) (hfm : Measurable f)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) (r : ℝ) (hr : r ≠ 0) :
    ∃ V : CoordinateSpace n → ℝ, ContDiff ℝ ∞ V ∧ ConvexOn ℝ univ V ∧
      (μ.prod (coordinateGaussian n)).map (fun p => p.1 + r • p.2) = potentialMeasure V := by
  haveI : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := hμ ▸ inferInstance
  have hmass : (∫ x, f x) = 1 := by
    have hlin : (∫⁻ x, ENNReal.ofReal (f x)) = 1 := by
      simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
        (measure_univ (μ := volume.withDensity (fun x => ENNReal.ofReal (f x))))
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf.1) hfm.aestronglyMeasurable, hlin]
    simp
  have hfi := integrable_of_integral_eq_one hmass
  obtain ⟨g,hgd,hgl,hgp,hgmap⟩ := coordinateGaussian_scaled_smooth_density r hr
  let q := f ⋆ g
  have hqd : ContDiff ℝ ∞ q := coordinate_convolution_contDiff hfi hgd (le_max_right R 0)
    (fun y hy => hs y ((le_max_left R 0).trans_lt hy))
  have hql : IsLogConcave q := coordinate_convolution_logconcave hf hgl hfm hgd.continuous.measurable hs
  have hqp : ∀ x, 0 < q x := coordinate_convolution_pos hf.1 hfi (by rw [hmass]; norm_num) hgp hgd.continuous hs
  let V := fun x => -Real.log (q x)
  refine ⟨V, (hqd.log (fun x => (hqp x).ne')).neg,
    convexOn_neg_log hql convex_univ (fun x _ => hqp x), ?_⟩
  rw [map_add_scaled_eq_convolution, hgmap, hμ,
    coordinate_convolution_withDensity_eq hf.1 hgl.1 hfm hgd.continuous.measurable hfi hgd.continuous hs]
  unfold potentialMeasure
  congr 1
  funext x
  simp only [V, neg_neg, Real.exp_log (hqp x)]
  rfl

end GaussianTilt.Letwin
