import GaussianTilt.MomentMapRegularityBallHessian

/-! # Translation-invariant ball-target maximum-principle geometry -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def subtractPlane (φ : E n → ℝ) (c : E n) (x : E n) : ℝ := φ x - inner ℝ c x

lemma gradient_subtractPlane {φ : E n → ℝ} (hd : Differentiable ℝ φ) (c x : E n) :
    gradient (subtractPlane φ c) x = gradient φ x - c := by
  have hf : HasFDerivAt (subtractPlane φ c)
      ((InnerProductSpace.toDual ℝ (E n)) (gradient φ x) -
        (InnerProductSpace.toDual ℝ (E n)) c) x :=
    (hd x).hasGradientAt.hasFDerivAt.sub (innerSL ℝ c).hasFDerivAt
  simpa only [map_sub, (InnerProductSpace.toDual ℝ (E n)).symm_apply_apply]
    using hf.hasGradientAt.gradient

lemma conjugateValues_subtractPlane (φ : E n → ℝ) (c p : E n) :
    conjugateValues (subtractPlane φ c) p = conjugateValues φ (p + c) := by
  unfold conjugateValues
  congr 1
  funext x
  simp only [subtractPlane, inner_add_left]
  ring

lemma conjugate_subtractPlane (φ : E n → ℝ) (c p : E n) :
    conjugate (subtractPlane φ c) p = conjugate φ (p + c) := by
  unfold conjugate
  rw [conjugateValues_subtractPlane]

/-- The endpoint gradient gap vanishes for a genuine moment transport to a
ball with any center. Centering a target therefore preserves the complete
infinity argument needed for the Hessian maximum principle. -/
theorem gradient_gap_of_translated_ball_transport {φ V : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    (c : E n) {R : ℝ} (hR : 0 < R) (hV : ContinuousOn V (Metric.ball c R))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x))) (h : E n) :
    Tendsto (fun x => gradient φ (x + h) - gradient φ (x + -h))
      (cocompact (E n)) (𝓝 0) := by
  let ψ := subtractPlane φ c
  have hψc : ConvexOn ℝ univ ψ := hc.sub ((innerSL ℝ c).toLinearMap.concaveOn convex_univ)
  have hψd : Differentiable ℝ ψ := hd.sub (innerSL ℝ c).differentiable
  have hψg : ∀ x, ‖gradient ψ x‖ ≤ R := by
    intro x
    have hp := supportsAt_mem_closure_of_ae_gradient hL hc (convex_ball c R)
      (ae_gradient_mem_of_target_density hL.continuous Metric.isOpen_ball hV hmap)
      (supportsAt_gradient hc (hd x))
    rw [closure_ball c hR.ne'] at hp
    rw [gradient_subtractPlane hd]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hp
  obtain ⟨hfinite, _, hconj, _⟩ := conjugate_regular_on_target hL.continuous hc
    Metric.isOpen_ball (convex_ball c R) hV hmap
  have hψfinite : ∀ p ∈ Metric.ball (0 : E n) R, BddAbove (conjugateValues ψ p) := by
    intro p hp
    rw [conjugateValues_subtractPlane]
    apply hfinite
    simpa [Metric.mem_ball, dist_eq_norm] using hp
  have hψlocal : ∀ r, 0 < r → r < R → ∃ M, ∀ p, ‖p‖ ≤ r → conjugate ψ p ≤ M := by
    intro r hr hrR
    have hsub : Metric.closedBall c r ⊆ Metric.ball c R := Metric.closedBall_subset_ball hrR
    obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn (hconj.mono hsub)
    refine ⟨M, fun p hp => ?_⟩
    rw [conjugate_subtractPlane]
    exact (le_abs_self _).trans (hM (p + c) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hp))
  have hrec := source_recession_tendsto_ball hψc hψd hR hψg hψfinite hψlocal
  have hgap := gradient_translation_gap_of_radial_asymptotic
    (gradient_radial_asymptotic hψc hψd hR hψg hrec) h
  convert hgap using 1
  funext x
  simp only [ψ, gradient_subtractPlane hd]
  abel

open GaussianTilt.Letwin

/-- The complete weak Hessian estimate for translated-ball targets,
including the centering performed in the regular approximation. -/
theorem translated_ball_hessian_entries_bound {φ V : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 2 φ)
    (c : E n) {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hV : ContinuousOn V (Metric.ball c R))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x)))
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
  apply secondDifference_decay_of_gradient_gap hcc (hφc.differentiable (by norm_num)) h
  have hd := hφ.differentiable (by norm_num)
  have hgap := gradient_gap_of_translated_ball_transport hL hc hd c hR hV hmap ((coordinateEquiv n).symm h)
  have hgap' := hgap.comp (coordinateEquiv n).symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have hout := (coordinateEquiv n).continuous.continuousAt.tendsto.comp hgap'
  simpa only [Function.comp_def, coordinateGradient_pullback hd, map_add, map_neg, map_sub, map_zero]
    using hout

end GaussianTilt.MomentMapRegularity
