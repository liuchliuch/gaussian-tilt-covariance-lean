import GaussianTilt.MomentMapSchauderSmoothBootstrap

/-! # Smooth source bootstrap from genuinely local Hölder exponents

The first source exponent may depend on the center. Each local exponent
first gives C³. That proved C³ regularity then supplies a common exponent
1/2 locally by the actual compact C¹-to-Hölder estimate.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open Set MeasureTheory
open scoped ContDiff Gradient
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

theorem moment_source_contDiff_infty_of_local_exponents [NeZero n]
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hV : ContDiffOn ℝ ∞ V Ω) (hgrad : ∀ x, gradient φ x ∈ Ω)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det= -φ x+V (gradient φ x))
    (hloc : ∀ a : KernelSpace n, ∃ R H α : ℝ, 0 < R ∧ 0 ≤ H ∧ 0 < α ∧ α < 1 ∧
      ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
        ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ContDiff ℝ ∞ φ := by
  have hφ3 : ContDiff ℝ 3 φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro a
    obtain ⟨R, H, α, hR, hH, hα, hα1, hh⟩ := hloc a
    obtain ⟨r, C, hr, _, _, hc, _⟩ := exists_moment_source_third_order_holder hφ hΩ hΩc
      (contDiffOn_infty.mp hV 2) hgrad hpos hMA a hR hH hα hα1 hh
    exact hc.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ3.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  apply moment_source_contDiff_infty hφ hΩ hΩc hV hgrad hpos hMA
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  intro a
  obtain ⟨C, hC, _, hh⟩ := exists_contDiff_holder_bound_on_compact_convex hD2
    (isCompact_closedBall a 2) (convex_closedBall a 2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  exact ⟨1, C, by norm_num, hC.le, by simpa only [mul_one] using hh⟩

/-- Source-factory endpoint allowing a different first Hessian Hölder
exponent at every center. Positivity and the classical equation still come
from the true moment transport after the first C² stage. -/
theorem moment_source_contDiff_infty_of_transport_local_exponents [NeZero n]
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hV : ContDiffOn ℝ ∞ V Ω) (hgrad : ∀ x, gradient φ x ∈ Ω)
    (hc : StrictConvexOn ℝ univ (coordinatePullback φ))
    {f : CoordinateSpace n → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hVc : Continuous (fun x => coordinatePullback V (coordinateGradient (coordinatePullback φ) x)))
    (hvalue : ∀ x, f (coordinateGradient (coordinatePullback φ) x)=
      Real.exp (-coordinatePullback V (coordinateGradient (coordinatePullback φ) x)))
    (hmap : momentMeasure (coordinatePullback φ)=volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hloc : ∀ a : KernelSpace n, ∃ R H α : ℝ, 0 < R ∧ 0 ≤ H ∧ 0 < α ∧ α < 1 ∧
      ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
        ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ContDiff ℝ ∞ φ := by
  have hφc : ContDiff ℝ 2 (coordinatePullback φ) := hφ.comp (coordinateEquiv n).symm.contDiff
  obtain ⟨hpos, hMA⟩ := posDef_and_mongeAmpere_of_strictConvex_transport hφc hc hfm hfn hVc hvalue hmap
  obtain ⟨hepos, heMA⟩ := euclidean_source_equation_of_coordinate hφ hpos hMA
  exact moment_source_contDiff_infty_of_local_exponents hφ hΩ hΩc hV hgrad hepos heMA hloc

end GaussianTilt.MomentMapSchauder
