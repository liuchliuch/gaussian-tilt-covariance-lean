import GaussianTilt.MomentMapSchauderLocalJetGain

/-!
# Genuine smooth source bootstrap after the first C²,α stage

The first gain uses the actual nonlinear finite-difference equation. Each
subsequent gain uses the literally differentiated source PDE, derived
Hölder forcing jets, the proved linear Schauder gain, and finite-basis
reconstruction of the new true derivative tensor. No smoothness or elliptic
regularity theorem is passed as a parameter.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2400000
open Set MeasureTheory
open scoped ContDiff Gradient
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- Complete smooth bootstrap for the actual moment-map equation after a
genuine first C²,α stage. The target may be smooth only on its open convex
domain; no global target derivative bounds are assumed. -/
theorem moment_source_contDiff_infty [NeZero n]
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hV : ContDiffOn ℝ ∞ V Ω) (hgrad : ∀ x, gradient φ x ∈ Ω)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det= -φ x+V (gradient φ x))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hloc : ∀ a : KernelSpace n, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧
      ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
        ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ContDiff ℝ ∞ φ := by
  have hV2 : ContDiffOn ℝ 2 V Ω := contDiffOn_infty.mp hV 2
  have hφ3 : ContDiff ℝ 3 φ := moment_source_contDiff_three hφ hΩ hΩc hV2 hgrad hpos hMA hα hα1 hloc
  have hlocal3 : ∀ a : KernelSpace n, ∃ R : ℝ, 0 < R ∧ HolderJetOn α 3 φ (Metric.closedBall a (2*R)) := by
    intro a
    obtain ⟨R, H, hR, hH, hφH⟩ := hloc a
    obtain ⟨r, C, hr, _, hC, _, hb, hh⟩ := exists_moment_source_third_order_holder
      hφ hΩ hΩc hV2 hgrad hpos hMA a hR hH hα hα1 hφH
    have hsub : Metric.closedBall a (r/2) ⊆ Metric.ball a r := Metric.closedBall_subset_ball (by linarith)
    have hthird : BoundedHolderOn α (fderiv ℝ (fderiv ℝ (fderiv ℝ φ))) (Metric.closedBall a (r/2)) :=
      ⟨C, hC.le, fun x hx => hb x (hsub hx), fun x hx y hy => hh x (hsub hx) y (hsub hy)⟩
    have hj := holderJetOn_of_top hφ3 (isCompact_closedBall a (r/2)) (convex_closedBall a (r/2))
      hα.le hα1.le (boundedHolderOn_iteratedFDeriv_three hthird)
    refine ⟨r/4, by positivity, ?_⟩
    have he : 2*(r/4)=r/2 := by ring
    simpa only [he] using hj
  have hind : ∀ k : ℕ, ContDiff ℝ (↑(k+3) : WithTop ℕ∞) φ ∧
      ∀ a : KernelSpace n, ∃ R : ℝ, 0 < R ∧ HolderJetOn α (k+3) φ (Metric.closedBall a (2*R)) := by
    intro k
    induction k with
    | zero => exact ⟨hφ3, hlocal3⟩
    | succ k ih =>
      have hVk : ContDiffOn ℝ (↑(k+3) : WithTop ℕ∞) V Ω := contDiffOn_infty.mp hV (k+3)
      have hnext := moment_source_contDiff_succ k ih.1 hΩ hVk hgrad hpos hMA hα hα1 ih.2
      refine ⟨hnext, ?_⟩
      intro a
      obtain ⟨R, hR, hj⟩ := ih.2 a
      exact exists_source_next_holderJetOn k ih.1 hnext hΩ hVk hgrad hpos hMA a hR hα hα1 hj
  apply contDiff_infty.mpr
  intro k
  exact (hind k).1.of_le (by exact_mod_cast (show k ≤ k+3 by omega))

/-- Smoothness from literal moment transport, with positive definiteness
and the classical Monge–Ampère identity derived only after first C²,α
regularity. This is the source-factory bootstrap endpoint. -/
theorem moment_source_contDiff_infty_of_transport [NeZero n]
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hV : ContDiffOn ℝ ∞ V Ω) (hgrad : ∀ x, gradient φ x ∈ Ω)
    (hc : StrictConvexOn ℝ univ (coordinatePullback φ))
    {f : CoordinateSpace n → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hVc : Continuous (fun x => coordinatePullback V (coordinateGradient (coordinatePullback φ) x)))
    (hvalue : ∀ x, f (coordinateGradient (coordinatePullback φ) x)=
      Real.exp (-coordinatePullback V (coordinateGradient (coordinatePullback φ) x)))
    (hmap : momentMeasure (coordinatePullback φ)=volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hloc : ∀ a : KernelSpace n, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧
      ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
        ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ContDiff ℝ ∞ φ := by
  have hφc : ContDiff ℝ 2 (coordinatePullback φ) := hφ.comp (coordinateEquiv n).symm.contDiff
  obtain ⟨hpos, hMA⟩ := posDef_and_mongeAmpere_of_strictConvex_transport hφc hc hfm hfn hVc hvalue hmap
  obtain ⟨hepos, heMA⟩ := euclidean_source_equation_of_coordinate hφ hpos hMA
  exact moment_source_contDiff_infty hφ hΩ hΩc hV hgrad hepos heMA hα hα1 hloc

end GaussianTilt.MomentMapSchauder
