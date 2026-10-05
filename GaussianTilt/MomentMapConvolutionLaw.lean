import GaussianTilt.MomentMapRegularization
import GaussianTilt.LinearImageDensity

/-!
# Density identification for actual independent perturbations

The smooth convolution densities in `MomentMapRegularization` are identified
with the measures used in the proved moment-convergence construction. Haar
transport constructs the scaled Gaussian density; convolution and restriction
are equalities of actual measures.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators Convolution ContDiff
namespace GaussianTilt.MomentMapApproximation
open Paouris LogConcaveMarginal
variable {n : ℕ}

theorem integral_density_eq_one {g : Reference.Space n → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hm : Measurable g)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (g x)))] :
    (∫ x, g x) = 1 := by
  have hlin : (∫⁻ x, ENNReal.ofReal (g x)) = 1 := by
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
      (measure_univ (μ := volume.withDensity (fun x => ENNReal.ofReal (g x))))
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg) hm.aestronglyMeasurable, hlin]
  simp

theorem exists_smooth_density_map_standardGaussian
    (e : Reference.Space n ≃L[ℝ] Reference.Space n) :
    ∃ g : Reference.Space n → ℝ, ContDiff ℝ ∞ g ∧ IsLogConcave g ∧
      (∀ x, 0 < g x) ∧ (∫ x, g x) = 1 ∧
      (standardGaussian n).map e = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
  obtain ⟨c, hc, hl, hm, hmap⟩ := LinearImageDensity.exists_density_map_linearEquiv
    e volume volume (standardGaussianDensity_logconcave n)
    (standardGaussianDensity_continuous n).measurable
  let g := fun x => c * standardGaussianDensity n (e.symm x)
  have hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
    rw [← hmap]
    change IsProbabilityMeasure ((standardGaussian n).map e)
    exact Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  letI := hprob
  refine ⟨g, contDiff_const.mul ((standardGaussianDensity_contDiff n).comp e.symm.contDiff),
    hl, fun x => mul_pos hc (standardGaussianDensity_pos _),
    integral_density_eq_one hl.1 hm, hmap⟩

theorem convolution_withDensity_eq {f g : Reference.Space n → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfi : Integrable f) (hgc : Continuous g)
    {R : ℝ} (hs : ∀ y, R < ‖y‖ → f y = 0) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))) ∗
      (volume.withDensity (fun x => ENNReal.ofReal (g x))) =
    volume.withDensity (fun x => ENNReal.ofReal ((f ⋆ g) x)) := by
  rw [conv_withDensity_eq_lconvolution hfm.ennreal_ofReal hgm.ennreal_ofReal]
  congr 1
  funext x
  rw [lconvolution_def]
  have hi : Integrable (fun y => f y * g (x - y)) :=
    (hasCompactSupport_of_bounded_support hs).convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hfi.locallyIntegrable hgc x
  change (∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (g (-y + x))) =
    ENNReal.ofReal (∫ y, f y * g (x - y))
  simp_rw [show ∀ y : Reference.Space n, -y + x = x - y by intro y; abel,
    ← ENNReal.ofReal_mul (hf _)]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun y => mul_nonneg (hf y) (hg (x - y))))).symm

theorem map_perturb_eq_convolution (μ ν : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (k : ℕ) :
    (μ.prod ν).map (perturb k) =
      μ ∗ (ν.map (fun z => ((k : ℝ) + 1)⁻¹ • z)) := by
  rw [Measure.conv]
  have hprod := Measure.map_prod_map μ ν measurable_id
    (show Measurable (fun z : Reference.Space n => ((k : ℝ) + 1)⁻¹ • z) by fun_prop)
  simp only [Measure.map_id] at hprod
  rw [hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem perturbedTruncation_eq_cond (μ ν : Measure (Reference.Space n)) (k : ℕ) :
    perturbedTruncation μ ν k =
      cond ((μ.prod ν).map (perturb k)) (Metric.ball 0 ((k : ℝ) + 1)) := by
  have hpre : perturb (E := Reference.Space n) k ⁻¹' Metric.ball 0 ((k : ℝ) + 1) =
      truncationEvent k := by
    ext p
    simp [truncationEvent, Metric.mem_ball, dist_zero_right]
  rw [perturbedTruncation, ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.map_smul, Measure.restrict_map (continuous_perturb k).measurable Metric.isOpen_ball.measurableSet,
    Measure.map_apply (continuous_perturb k).measurable Metric.isOpen_ball.measurableSet, hpre]

theorem cond_withDensity_eq_indicator_div {g : Reference.Space n → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hm : Measurable g)
    {S : Set (Reference.Space n)} (hS : MeasurableSet S)
    (hpos : 0 < (volume.withDensity (fun x => ENNReal.ofReal (g x))) S)
    (hfin : (volume.withDensity (fun x => ENNReal.ofReal (g x))) S ≠ ⊤) :
    cond (volume.withDensity (fun x => ENNReal.ofReal (g x))) S =
      volume.withDensity (fun x => ENNReal.ofReal (S.indicator
        (fun y => g y / (volume.withDensity (fun z => ENNReal.ofReal (g z)) S).toReal) x)) := by
  let m := volume.withDensity (fun x => ENNReal.ofReal (g x)) S
  have hmp : 0 < m.toReal := ENNReal.toReal_pos hpos.ne' hfin
  have heq : (fun x => ENNReal.ofReal (S.indicator (fun y => g y / m.toReal) x)) =
      m⁻¹ • S.indicator (fun x => ENNReal.ofReal (g x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx, Pi.smul_apply, smul_eq_mul]
      rw [ENNReal.ofReal_div_of_pos hmp, ENNReal.ofReal_toReal hfin]
      exact ENNReal.div_eq_inv_mul
    · simp [hx]
  change _ = volume.withDensity (fun x => ENNReal.ofReal (S.indicator (fun y => g y / m.toReal) x))
  rw [heq, withDensity_smul _ (hm.ennreal_ofReal.indicator hS), withDensity_indicator hS,
    ← restrict_withDensity hS]
  rfl

/-- The normalized restriction of a smooth positive logconcave density to
any positive-radius ball has the exact regular target-potential form in A1. -/
theorem exists_smooth_convex_potential_cond_ball {g : Reference.Space n → ℝ}
    (hgd : ContDiff ℝ ∞ g) (hgl : IsLogConcave g) (hgp : ∀ x, 0 < g x)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (g x)))]
    {r : ℝ} (hr : 0 < r) :
    ∃ V : Reference.Space n → ℝ, ContDiff ℝ ∞ V ∧ ConvexOn ℝ univ V ∧
      cond (volume.withDensity (fun x => ENNReal.ofReal (g x))) (Metric.ball 0 r) =
        volume.withDensity (fun x => ENNReal.ofReal
          ((Metric.ball 0 r).indicator (fun y => Real.exp (-V y)) x)) := by
  let ρ := volume.withDensity (fun x => ENNReal.ofReal (g x))
  have hac : (volume : Measure (Reference.Space n)) ≪ ρ :=
    withDensity_absolutelyContinuous' hgd.continuous.measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (hgp x)).ne'))
  letI : ρ.IsOpenPosMeasure := hac.isOpenPosMeasure
  have hp : 0 < ρ (Metric.ball 0 r) :=
    Metric.isOpen_ball.measure_pos ρ ⟨0, Metric.mem_ball_self hr⟩
  let m := (ρ (Metric.ball 0 r)).toReal
  have hmp : 0 < m := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  let V := fun x => -Real.log (g x) + Real.log m
  have hVd : ContDiff ℝ ∞ V := (hgd.log (fun x => (hgp x).ne')).neg.add contDiff_const
  have hVc : ConvexOn ℝ univ V :=
    (convexOn_neg_log hgl convex_univ (fun x _ => hgp x)).add_const (Real.log m)
  refine ⟨V, hVd, hVc, ?_⟩
  rw [cond_withDensity_eq_indicator_div hgl.1 hgd.continuous.measurable
    Metric.isOpen_ball.measurableSet hp (measure_ne_top _ _)]
  congr 1
  funext x
  congr 1
  by_cases hx : x ∈ Metric.ball (0 : Reference.Space n) r
  · simp only [indicator_of_mem hx]
    change g x / m = Real.exp (-(-Real.log (g x) + Real.log m))
    rw [show -(-Real.log (g x) + Real.log m) = Real.log (g x) - Real.log m by ring,
      Real.exp_sub, Real.exp_log (hgp x), Real.exp_log hmp]
  · simp only [indicator_of_notMem hx]

end GaussianTilt.MomentMapApproximation
