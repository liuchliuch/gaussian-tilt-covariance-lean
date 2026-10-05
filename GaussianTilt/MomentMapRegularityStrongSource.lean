import GaussianTilt.MomentMapRegularityTranslatedBall
import GaussianTilt.MomentMapRegularityAffineTransport
import GaussianTilt.MomentMapRegularityLocalizationConclusion
import GaussianTilt.MomentMapCoordinateTransport
import GaussianTilt.MomentMapExistence
import GaussianTilt.LetwinRegularApproximation

/-! # The strong-ball regular source bridge

Weak source existence, strict convexity, coordinate transport, pointwise
Monge--Ampère, positive Hessian, infinity geometry, global Hessian bounds and
linear whitening are all proved. Only source C∞ smoothness remains explicit
in the final conditional constructor; it is not asserted in this file.
-/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators Topology ContDiff NNReal ENNReal Gradient
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma ball_density_eq_closedBall (V : E n → ℝ) (c : E n) {R : ℝ} (hR : 0 < R) :
    volume.withDensity (fun x => ENNReal.ofReal
      ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x)) =
    volume.withDensity (fun x => ENNReal.ofReal
      ((Metric.closedBall c R).indicator (fun y => Real.exp (-V y)) x)) := by
  apply withDensity_congr_ae
  filter_upwards [ae_mem_of_mem_closure_target (Metric.isOpen_ball : IsOpen (Metric.ball c R))
    (convex_ball c R)] with x hx
  by_cases hxb : x ∈ Metric.ball c R
  · simp only [indicator_of_mem hxb, indicator_of_mem (Metric.ball_subset_closedBall hxb)]
  · have hxc : x ∉ Metric.closedBall c R := by
      intro hxc
      apply hxb
      apply hx
      rwa [closure_ball c hR.ne']
    simp only [indicator_of_notMem hxb, indicator_of_notMem hxc]

/-- For a genuine smooth moment source of a strongly convex translated-ball
target, all remaining regular-source data are derived. -/
theorem regular_source_of_smooth_strong_ball_transport {φ V : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ ∞ φ)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))))]
    (c : E n) {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hV : ContDiff ℝ ∞ V) (hVc : StrongConvexOn univ κ V)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x))) :
    Nonempty (RegularMomentSource ((coordinateEquiv n) '' Metric.ball c R)
      ((volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x))).map (coordinateEquiv n))) := by
  have hstrict := strictConvexOn_of_target_density hL hc Metric.isOpen_ball (convex_ball c R)
    Metric.isBounded_ball hV.continuous.continuousOn hmap
  have hφ2 := contDiff_infty.mp hφ 2
  have hφraw := contDiff_coordinatePullback hφ
  have hstrictRaw := strictConvex_coordinatePullback hstrict
  have hrawMap := coordinate_moment_transport (contDiff_infty.mp hφ 1) hmap
  let f : CoordinateSpace n → ℝ := fun x => (Metric.closedBall c R).indicator
    (fun y => Real.exp (-V y)) ((coordinateEquiv n).symm x)
  have hclosedMap : momentMeasure (coordinatePullback φ) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [hrawMap, ball_density_eq_closedBall V c hR, map_density_coordinateEquiv]
  have hfm : Measurable f :=
    ((Real.continuous_exp.comp hV.continuous.neg).measurable.indicator
      Metric.isClosed_closedBall.measurableSet).comp (coordinateEquiv n).symm.continuous.measurable
  have hfn : ∀ x, 0 ≤ f x := fun x => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hg (x : E n) : gradient φ x ∈ Metric.closedBall c R := by
    have h := supportsAt_mem_closure_of_ae_gradient hL hc (convex_ball c R)
      (ae_gradient_mem_of_target_density hL.continuous Metric.isOpen_ball hV.continuous.continuousOn hmap)
      (supportsAt_gradient hc (hφ2.differentiable (by norm_num) x))
    rwa [closure_ball c hR.ne'] at h
  have hvalue (x : CoordinateSpace n) : f (coordinateGradient (coordinatePullback φ) x) =
      Real.exp (-coordinatePullback V (coordinateGradient (coordinatePullback φ) x)) := by
    change (Metric.closedBall c R).indicator (fun y => Real.exp (-V y))
      ((coordinateEquiv n).symm (coordinateGradient (coordinatePullback φ) x)) =
      Real.exp (-V ((coordinateEquiv n).symm (coordinateGradient (coordinatePullback φ) x)))
    rw [coordinateGradient_pullback (hφ2.differentiable (by norm_num)),
      (coordinateEquiv n).symm_apply_apply, indicator_of_mem (hg _)]
  have hVgc : Continuous (fun x => coordinatePullback V (coordinateGradient (coordinatePullback φ) x)) :=
    (contDiff_coordinatePullback hV).continuous.comp
      (continuous_coordinateGradient (contDiff_infty.mp hφraw 1))
  obtain ⟨hH, hMA⟩ := posDef_and_mongeAmpere_of_strictConvex_transport
    (contDiff_infty.mp hφraw 2) hstrictRaw hfm hfn hVgc hvalue hclosedMap
  have hbounded := translated_ball_hessian_entries_bound hL hc hφ2 c hR hκ hV.continuous.continuousOn
    hmap (stronglyConvex_coordinatePullback hκ.le hVc) hH hMA
  exact ⟨{
    potential := coordinatePullback φ
    probability := coordinate_source_probability φ
    smooth := hφraw
    strict_convex := hstrictRaw
    hessian_bounded := ⟨_, hbounded⟩
    transport := hrawMap }⟩

/-- The final constructor has only the genuinely remaining smoothness step
as an explicit input. Weak source existence and every other regular-source
property are constructed in the proof. -/
theorem regular_strong_ball_source_of_smoothness
    (V : E n → ℝ) (c : E n) {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hV : ContDiff ℝ ∞ V) (hVc : StrongConvexOn univ κ V)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal
      ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x)))]
    (hmean : (∫ x : E n, x ∂volume.withDensity (fun x => ENNReal.ofReal
      ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x))) = 0)
    (hsmooth : ∀ (φ : E n → ℝ) (L : ℝ≥0), LipschitzWith L φ → ConvexOn ℝ univ φ →
      IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) →
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map (gradient φ) =
        volume.withDensity (fun x => ENNReal.ofReal
          ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x)) → ContDiff ℝ ∞ φ) :
    Nonempty (RegularMomentSource ((coordinateEquiv n) '' Metric.ball c R)
      ((volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x))).map (coordinateEquiv n))) := by
  letI : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal
      (MomentMapCoercivity.regularTargetDensity (Metric.ball c R) V x))) := by
    simpa only [MomentMapCoercivity.regularTargetDensity] using
      (inferInstance : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x))))
  obtain ⟨φ, L, hL, hc, hprob, hmap⟩ := MomentMapCoercivity.exists_moment_source_for_regular_target
    Metric.isOpen_ball (convex_ball c R) Metric.isBounded_ball hV.continuous.continuousOn hmean
  letI := hprob
  have hφ := hsmooth φ L hL hc hprob hmap
  exact regular_source_of_smooth_strong_ball_transport hL hc hφ c hR hκ hV hVc hmap

/-- The regular source data pass through the actual covariance-whitening
matrix. No regularity or Hessian estimate is newly assumed here. -/
theorem regular_source_linear_image {D : Set (CoordinateSpace n)} {μ : Measure (CoordinateSpace n)}
    (S : RegularMomentSource D μ) (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.det ≠ 0) :
    Nonempty (RegularMomentSource (coordinateMatrixMap T '' D) (μ.map (coordinateMatrixMap T))) := by
  letI := S.probability
  obtain ⟨B, hB⟩ := S.hessian_bounded
  obtain ⟨ψ, hprob, hsm, hcv, hbound, hmap⟩ :=
    exists_linear_image_moment_source S.smooth S.strict_convex hB T hT
  refine ⟨⟨ψ, hprob, hsm, hcv, hbound, ?_⟩⟩
  rw [hmap, S.transport]

end GaussianTilt.MomentMapRegularity
