import GaussianTilt.MomentMapRegularityImprovementStep
import GaussianTilt.MomentMapRegularityReferenceC2Equation

/-! # Actual normalized reference representatives for improvement -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxSize 1000

/-- A genuine smooth unit-density reference supplies the actual global
representative and Taylor data consumed by the normalization step. The
representative is built by a cutoff inside the section; its Hessian and
Jacobian are preserved at the center. -/
theorem exists_reference_improvement_representative [NeZero n]
    {w : E n → ℝ} (hwc : Continuous w) {S : Set (E n)} (hS : IsCompact S)
    (hw : ContDiffOn ℝ ∞ w (interior S)) (hc : ConvexOn ℝ S w)
    (hb : ∀ y ∈ frontier S, w y=0)
    (hMA : ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A)
    {r R : ℝ} (hr : 0<r) (hR : 0≤R) (hSR : S⊆Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0:E n) r⊆interior S) (c : ℝ) :
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧
      (∀ y, ‖y‖≤r/2 → v y=w y+c) ∧
      (coordinateHessian (coordinatePullback v) 0).PosDef ∧
      (coordinateHessian (coordinatePullback v) 0).det=1 ∧
      ∀ y, ‖y‖≤r/2 →
        |v y-quadraticJet (v 0) (gradient v 0) 0 (frechetHessian v 0) y|≤
          referenceTaylorConstant n r R*‖y‖^3 := by
  have hclassical := positive_hessian_and_unit_det_of_C2_alexandrov hc isOpen_interior
    (Subset.refl (interior S)) (contDiffOn_infty.mp hw 2) hMA
  have hPD := fun y hy => (hclassical y hy).1
  have hdet := fun y hy => (hclassical y hy).2
  let K := Metric.closedBall (0:E n) (r/2)
  have hKS : K⊆interior S := (Metric.closedBall_subset_closedBall (by linarith)).trans hrS
  obtain ⟨v,hv,he⟩ := exists_global_smooth_eq_near_compact isOpen_interior
    (hw.add contDiffOn_const) (isCompact_closedBall _ _) hKS (u:=fun y=>w y+c)
  have heq (y : E n) (hy : y∈K) : v y=w y+c := (he y hy).self_of_nhds
  have hraw (y : E n) (hy : y∈K) : coordinatePullback v =ᶠ[𝓝 (coordinateEquiv n y)]
      (fun z=>coordinatePullback w z+c) := by
    have hh := coordinatePullback_congr_nhds (he y hy)
    exact hh
  have hz : (0:E n)∈K := by simp only [K,Metric.mem_closedBall,dist_self]; positivity
  have hHz : coordinateHessian (coordinatePullback v) 0=coordinateHessian (coordinatePullback w) 0 := by
    have hh := coordinateHessian_congr_nhds (hraw 0 hz)
    simpa only [map_zero,coordinateHessian_add_const] using hh
  have hthird := (smooth_reference_derivative_bounds_on_half_ball hwc hS hw hc hb hMA hPD hdet hr hR hSR hrS).2
  have hvthird : ∀ y∈K, ∀ i j k,
      |coordinateThirdDerivative (coordinatePullback v) (coordinateEquiv n y) i j k|≤ max (referenceThirdBound n r R) 0 := by
    intro y hy i j k
    rw [coordinateThirdDerivative_congr_nhds (hraw y hy),coordinateThirdDerivative_add_const]
    exact (hthird y hy i j k).trans (le_max_left _ _)
  refine ⟨v,hv,fun y hy=>heq y (by simpa [K] using hy),?_,?_,?_⟩
  · rw [hHz]
    simpa only [map_zero] using hPD 0 (hKS hz)
  · rw [hHz]
    simpa only [map_zero] using hdet 0 (hKS hz)
  · intro y hy
    have hyK : y∈K := by simpa [K] using hy
    have ht := euclidean_taylor_of_coordinateThird_bound (contDiff_infty.mp hv 3)
      (convex_closedBall _ _) (le_max_right _ _) hvthird (x:=0) (h:=y) hz (by simpa [K] using hyK)
    convert ht using 1 <;> simp only [quadraticJet,sub_zero,zero_add,inner_gradient_eq_fderiv,inner_frechetHessian,
      referenceTaylorConstant] <;> ring

end GaussianTilt.MomentMapRegularity
