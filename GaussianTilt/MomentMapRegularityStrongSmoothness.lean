import GaussianTilt.MomentMapRegularityImprovementTransport
import GaussianTilt.MomentMapRegularityStrongSource
import GaussianTilt.MomentMapSchauderLocalExponents
import GaussianTilt.LetwinStrongSourceBridge

/-! # The actual strong-ball source obligation reduced to classical inner references -/
noncomputable section
open Set MeasureTheory Matrix
open scoped NNReal ENNReal ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

theorem smooth_ball_moment_source_of_classical_references [NeZero n]
    {φ V : E n → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    (c : E n) {R : ℝ} (hR : 0 < R) (hV : ContDiff ℝ ∞ V)
    (hmap : (volume.withDensity (fun x=>ENNReal.ofReal (Real.exp (-φ x)))).map (gradient φ)=
      volume.withDensity (fun x=>ENNReal.ofReal ((Metric.ball c R).indicator (fun y=>Real.exp (-V y)) x)))
    (href : ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
      ∃ w : E n → ℝ, Continuous w ∧ ContDiffOn ℝ ∞ w (interior S) ∧ ConvexOn ℝ S w ∧
        (∀ y∈frontier S, w y=0) ∧
        ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A) :
    ContDiff ℝ ∞ φ := by
  obtain ⟨hφ2,hloc⟩ := moment_source_C2_holder_of_classical_references hL hc Metric.isOpen_ball
    (convex_ball c R) Metric.isBounded_ball (contDiff_infty.mp hV 1) hmap href
  have hstrict := strictConvexOn_of_target_density hL hc Metric.isOpen_ball (convex_ball c R)
    Metric.isBounded_ball hV.continuous.continuousOn hmap
  have hφ1 : ContDiff ℝ 1 φ := hφ2.of_le (by norm_num)
  have hrawMap := coordinate_moment_transport hφ1 hmap
  let f : CoordinateSpace n → ℝ := fun x=>(Metric.closedBall c R).indicator
    (fun y=>Real.exp (-V y)) ((coordinateEquiv n).symm x)
  have hclosedMap : momentMeasure (coordinatePullback φ)=volume.withDensity (fun x=>ENNReal.ofReal (f x)) := by
    rw [hrawMap,ball_density_eq_closedBall V c hR,map_density_coordinateEquiv]
  have hfm : Measurable f :=
    ((Real.continuous_exp.comp hV.continuous.neg).measurable.indicator
      Metric.isClosed_closedBall.measurableSet).comp (coordinateEquiv n).symm.continuous.measurable
  have hfn : ∀ x, 0≤f x := fun x=>indicator_nonneg (fun _ _=>(Real.exp_pos _).le) _
  have hg (x:E n) : gradient φ x∈Metric.closedBall c R := by
    have hh := supportsAt_mem_closure_of_ae_gradient hL hc (convex_ball c R)
      (ae_gradient_mem_of_target_density hL.continuous Metric.isOpen_ball hV.continuous.continuousOn hmap)
      (supportsAt_gradient hc (hφ2.differentiable (by norm_num) x))
    rwa [closure_ball c hR.ne'] at hh
  have hvalue (x:CoordinateSpace n) : f (coordinateGradient (coordinatePullback φ) x)=
      Real.exp (-coordinatePullback V (coordinateGradient (coordinatePullback φ) x)) := by
    change (Metric.closedBall c R).indicator (fun y=>Real.exp (-V y))
      ((coordinateEquiv n).symm (coordinateGradient (coordinatePullback φ) x))=_
    rw [coordinateGradient_pullback (hφ2.differentiable (by norm_num)),
      (coordinateEquiv n).symm_apply_apply,indicator_of_mem (hg _)]
    rfl
  have hVgc : Continuous (fun x=>coordinatePullback V (coordinateGradient (coordinatePullback φ) x)) :=
    (contDiff_coordinatePullback hV).continuous.comp
      (continuous_coordinateGradient (contDiff_coordinatePullback hφ1))
  exact moment_source_contDiff_infty_of_transport_local_exponents hφ2 isOpen_univ convex_univ
    hV.contDiffOn (fun _=>mem_univ _) (strictConvex_coordinatePullback hstrict)
    hfm hfn hVgc hvalue hclosedMap hloc

/-- Every other analytic and probabilistic component of the final compact
Letwin source obligation is already proved. This implication isolates the
remaining actual classical-reference construction without assuming source
smoothness, Hessian bounds, or the Monge--Ampère equation. -/
theorem strongBallSourceSmoothness_of_classical_references
    (href : ∀ (n:ℕ) [NeZero n], ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
      ∃ w : E n → ℝ, Continuous w ∧ ContDiffOn ℝ ∞ w (interior S) ∧ ConvexOn ℝ S w ∧
        (∀ y∈frontier S, w y=0) ∧
        ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A) :
    StrongBallSourceSmoothness := by
  intro n V c R κ hR hκ hV hVc φ L hL hc hprob hmap
  by_cases hn : n=0
  · subst n
    have he : φ=fun _=>φ 0 := by funext x; congr 1; exact Subsingleton.elim _ _
    rw [he]
    exact contDiff_const
  · letI : NeZero n := ⟨hn⟩
    exact smooth_ball_moment_source_of_classical_references hL hc c hR hV hmap (href n)

end GaussianTilt.MomentMapRegularity
