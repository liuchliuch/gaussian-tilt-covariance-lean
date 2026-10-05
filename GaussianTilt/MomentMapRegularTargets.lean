import GaussianTilt.MomentMapConvolutionLaw
import GaussianTilt.LogConcaveLinearImages

/-!
# Constructing the regular target laws in Letwin A1

Every Gaussian-perturbed and ball-conditioned compact logconcave law has a
genuinely constructed smooth convex target potential. This is a statement
about the target density `V`, not the source moment potential `φ`; it does
not assert moment-map existence or elliptic regularity.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators Convolution ContDiff
namespace GaussianTilt.MomentMapApproximation
open Paouris LogConcaveMarginal
variable {n : ℕ}

theorem exists_smooth_convex_potential_perturbedTruncation
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ) (k : ℕ) :
    ∃ V : Reference.Space n → ℝ, ContDiff ℝ ∞ V ∧ ConvexOn ℝ univ V ∧
      perturbedTruncation μ (standardGaussian n) k =
        volume.withDensity (fun x => ENNReal.ofReal
          ((Metric.ball 0 ((k : ℝ) + 1)).indicator (fun y => Real.exp (-V y)) x)) := by
  obtain ⟨f, R, hf, hfm, hfs, hμ⟩ := LogConcaveLinearImages.exists_compact_density hc hl
  haveI : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := hμ ▸ inferInstance
  have hmass : (∫ x, f x) = 1 := integral_density_eq_one hf.1 hfm
  have hfi := integrable_of_integral_eq_one hmass
  have hfs' : ∀ y, max R 0 < ‖y‖ → f y = 0 := fun y hy => hfs y ((le_max_left _ _).trans_lt hy)
  have hε : ((k : ℝ) + 1)⁻¹ ≠ 0 := by positivity
  let e : Reference.Space n ≃L[ℝ] Reference.Space n :=
    (LinearEquiv.smulOfNeZero ℝ (Reference.Space n) ((k : ℝ) + 1)⁻¹ hε).toContinuousLinearEquiv
  obtain ⟨g, hgd, hgl, hgp, hgint, hgmap⟩ := exists_smooth_density_map_standardGaussian e
  let q := f ⋆ g
  have hqd : ContDiff ℝ ∞ q := contDiff_convolution_of_bounded_support hfi hgd (le_max_right _ _) hfs'
  have hql : IsLogConcave q :=
    convolution_logconcave_of_bounded_support hf hgl hfm hgd.continuous.measurable hfs
  have hqp : ∀ x, 0 < q x := convolution_pos_of_positive_right hf.1 hfi
    (by rw [hmass]; norm_num) hgp hgd.continuous hfs
  have hmap : (μ.prod (standardGaussian n)).map (perturb k) =
      volume.withDensity (fun x => ENNReal.ofReal (q x)) := by
    rw [map_perturb_eq_convolution]
    change μ ∗ (standardGaussian n).map e = _
    rw [hgmap, hμ]
    exact convolution_withDensity_eq hf.1 hgl.1 hfm hgd.continuous.measurable hfi hgd.continuous hfs
  haveI : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (q x))) := by
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map (continuous_perturb k).measurable.aemeasurable
  obtain ⟨V, hVd, hVc, hVlaw⟩ := exists_smooth_convex_potential_cond_ball hqd hql hqp
    (by positivity : 0 < (k : ℝ) + 1)
  refine ⟨V, hVd, hVc, ?_⟩
  rw [perturbedTruncation_eq_cond, hmap, hVlaw]

end GaussianTilt.MomentMapApproximation
