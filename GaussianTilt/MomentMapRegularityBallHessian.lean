import GaussianTilt.MomentMapRegularityBall
import GaussianTilt.MomentMapRegularityHessian
import GaussianTilt.MomentMapRegularityLocalization

/-! # Ball-target maximum-principle geometry in integration-by-parts coordinates -/
noncomputable section
open MeasureTheory Filter Set WithLp
open scoped Topology BigOperators Gradient ContDiff NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

abbrev coordinateEquiv (n : ℕ) : E n ≃L[ℝ] CoordinateSpace n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

def coordinatePullback (φ : E n → ℝ) : CoordinateSpace n → ℝ :=
  φ ∘ (coordinateEquiv n).symm

lemma coordinateGradient_pullback {φ : E n → ℝ} (hd : Differentiable ℝ φ)
    (x : CoordinateSpace n) :
    coordinateGradient (coordinatePullback φ) x =
      coordinateEquiv n (gradient φ ((coordinateEquiv n).symm x)) := by
  ext i
  change fderiv ℝ (φ ∘ (coordinateEquiv n).symm) x (Pi.single i 1) = _
  rw [fderiv_comp x (hd _) (coordinateEquiv n).symm.differentiableAt,
    (coordinateEquiv n).symm.fderiv, ContinuousLinearMap.comp_apply]
  have he : fderiv ℝ φ ((coordinateEquiv n).symm x) =
      InnerProductSpace.toDual ℝ (E n) (gradient φ ((coordinateEquiv n).symm x)) := by
    rw [gradient, (InnerProductSpace.toDual ℝ (E n)).apply_symm_apply]
  rw [he]
  change inner ℝ (gradient φ ((coordinateEquiv n).symm x))
    (toLp 2 (Pi.single i 1)) = _
  simp [PiLp.inner_apply, Pi.single_apply, coordinateEquiv]

/-- Actual moment transport to a ball gives bounded gradients everywhere,
including at all points where source differentiability is known. -/
lemma gradient_norm_le_of_ball_transport {φ V : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    {R : ℝ} (hR : 0 < R) (hV : ContinuousOn V (Metric.ball 0 R))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball 0 R).indicator (fun y => Real.exp (-V y)) x))) (x : E n) :
    ‖gradient φ x‖ ≤ R := by
  have hp := supportsAt_mem_closure_of_ae_gradient hL hc (convex_ball (0 : E n) R)
    (ae_gradient_mem_of_target_density hL.continuous Metric.isOpen_ball hV hmap)
    (supportsAt_gradient hc (hd x))
  rw [closure_ball (0 : E n) hR.ne'] at hp
  simpa using hp

/-- The coordinate endpoint-gradient gap tends to zero for a genuine
ball-target source. This closes the infinity condition in the previously
proved quantitative maximum principle. -/
theorem coordinate_gradient_gap_of_ball_transport {φ V : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    {R : ℝ} (hR : 0 < R) (hV : ContinuousOn V (Metric.ball 0 R))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball 0 R).indicator (fun y => Real.exp (-V y)) x))) (h : CoordinateSpace n) :
    Tendsto (fun x => coordinateGradient (coordinatePullback φ) (x + h) -
      coordinateGradient (coordinatePullback φ) (x + -h))
      (cocompact (CoordinateSpace n)) (𝓝 0) := by
  have hasym := gradient_radial_asymptotic_of_ball_transport hL.continuous hc hd hR
    (gradient_norm_le_of_ball_transport hL hc hd hR hV hmap) hV hmap
  have hgap := gradient_translation_gap_of_radial_asymptotic hasym ((coordinateEquiv n).symm h)
  have hgap' := hgap.comp (coordinateEquiv n).symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hout := (coordinateEquiv n).continuous.continuousAt.tendsto.comp hgap'
  simpa only [Function.comp_def, coordinateGradient_pullback hd, map_add, map_neg, map_sub, map_zero]
    using hout

/-- A genuine ball-target moment transport closes the entire geometric
maximum-principle argument. Given a classical C² Monge--Ampère solution and
a strongly convex target, its Hessian entries are globally bounded. Neither
maximum attainment, source-gradient decay nor a Hessian bound is assumed. -/
theorem ball_target_hessian_entries_bound {φ V : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 2 φ)
    {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hV : ContinuousOn V (Metric.ball 0 R))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball 0 R).indicator (fun y => Real.exp (-V y)) x)))
    (hVc : StrongConvexOn univ κ (coordinatePullback V))
    (hH : ∀ x, (coordinateHessian (coordinatePullback φ) x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian (coordinatePullback φ) x).det =
      -coordinatePullback φ x + coordinatePullback V (coordinateGradient (coordinatePullback φ) x)) :
    ∀ x i j, |coordinateHessian (coordinatePullback φ) x i j| ≤ 4 * (n : ℝ)^2 / κ := by
  have hφc : ContDiff ℝ 2 (coordinatePullback φ) := hφ.comp (coordinateEquiv n).symm.contDiff
  have hcc : ConvexOn ℝ univ (coordinatePullback φ) := by
    simpa only [coordinatePullback, preimage_univ] using
      hc.comp_linearMap (coordinateEquiv n).symm.toLinearMap
  apply hessian_entries_bounded_of_secondDifference_decay hφc hcc hH hMA hκ hVc (fun _ => mem_univ _)
  intro h
  exact secondDifference_decay_of_gradient_gap hcc (hφc.differentiable (by norm_num)) h
    (coordinate_gradient_gap_of_ball_transport hL hc (hφ.differentiable (by norm_num)) hR hV hmap h)

/-- Euclidean target strong convexity implies strong convexity in the raw
coordinate sup norm, with the same constant. -/
lemma stronglyConvex_coordinatePullback {V : E n → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hV : StrongConvexOn univ κ V) : StrongConvexOn univ κ (coordinatePullback V) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hV.2 (mem_univ ((coordinateEquiv n).symm x))
    (mem_univ ((coordinateEquiv n).symm y)) ha hb hab
  have hn : ‖x - y‖ ≤ ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact PiLp.norm_apply_le ((coordinateEquiv n).symm x - (coordinateEquiv n).symm y) i
  have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ a * b * (κ / 2) by positivity)
  change coordinatePullback V (a • x + b • y) ≤
    a * coordinatePullback V x + b * coordinatePullback V y - a * b * (κ / 2 * ‖x - y‖^2)
  have he : (coordinateEquiv n).symm (a • x + b • y) =
    a • (coordinateEquiv n).symm x + b • (coordinateEquiv n).symm y := by simp
  change V ((coordinateEquiv n).symm (a • x + b • y)) ≤
    a * V ((coordinateEquiv n).symm x) + b * V ((coordinateEquiv n).symm y) -
      a * b * (κ / 2 * ‖x - y‖^2)
  rw [he]
  simp only [smul_eq_mul] at h
  nlinarith

end GaussianTilt.MomentMapRegularity
