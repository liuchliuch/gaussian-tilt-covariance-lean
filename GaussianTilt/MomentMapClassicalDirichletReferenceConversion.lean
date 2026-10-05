import GaussianTilt.MomentMapClassicalDirichletUniformExponentGlobal

/-! # Literal classical reference functions constructed from true solution jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- A positive genuine unit-determinant jet gives the exact Euclidean
classical Dirichlet reference required by the Alexandrov existence bridge.
The function is constructed, convexity and interior smoothness are proved,
and no extension of boundary derivatives is assumed. -/
theorem classical_unit_dirichlet_of_positive_holder_jet [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hp : ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef)
    (hMA : ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).det = 1) :
    ∃ u : E n → ℝ, Continuous u ∧ ContDiffOn ℝ ∞ u (interior d.body) ∧
      ConvexOn ℝ d.body u ∧ (∀ x ∈ frontier d.body, u x=0) ∧
      (∀ x ∈ interior d.body, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef) ∧
      (∀ x ∈ interior d.body, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det=1) := by
  let v := intrinsicValue d.coordinate_body_convex α j.1
  let u : E n → ℝ := v ∘ (coordinateEquiv n)
  have huc : Continuous u := (continuous_intrinsicValue_zeroBoundary d.coordinate_body_convex
    d.coordinate_body_compact.isClosed α j).comp (coordinateEquiv n).continuous
  have hvs : ContDiffOn ℝ ∞ v (interior {x | d.coordinateDefining x ≤ 0}) :=
    intrinsicValue_contDiffOn_infty_of_positive_density d.coordinate_body_convex hα hα1 j.1
      (ρ := fun _ => 1) contDiffOn_const (fun _ _ => zero_lt_one)
      (fun x hx => hp x (interior_subset hx)) (fun x hx => hMA x (interior_subset hx))
  have hus : ContDiffOn ℝ ∞ u (interior d.body) :=
    hvs.comp (coordinateEquiv n).contDiff.contDiffOn (fun x hx => d.coordinate_mem_interior_body hx)
  have hvc := intrinsicValue_convexOn_of_posSemidef d.coordinate_body_convex hα j.1
    (fun x hx => (hp x hx).posSemidef)
  have hconv : ConvexOn ℝ d.body u := by
    refine ⟨d.convex_body,?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hvc.2 (d.coordinate_mem_body hx) (d.coordinate_mem_body hy) ha hb hab
    simpa only [u,Function.comp_apply,map_add,map_smul] using hh
  have hzero (x : E n) (hx : x ∈ frontier d.body) : u x=0 := by
    have hraw : coordinateEquiv n x ∈ frontier {y | d.coordinateDefining y ≤ 0} := by
      rw [d.coordinate_body_frontier]
      change d.defining ((coordinateEquiv n).symm (coordinateEquiv n x))=0
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact d.defining_zero_of_mem_frontier_body hx
    exact zeroBoundary_value d.coordinate_body_convex d.coordinate_body_compact.isClosed α j hraw
  have he : coordinatePullback u=v := by
    funext x
    simp only [coordinatePullback,u,Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨u,huc,hus,hconv,hzero,?_,?_⟩
  · intro x hx
    rw [he,← intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 (d.coordinate_mem_interior_body hx)]
    exact hp _ (d.coordinate_mem_body (interior_subset hx))
  · intro x hx
    rw [he,← intrinsicHessian_eq_actual d.coordinate_body_convex hα j.1 (d.coordinate_mem_interior_body hx)]
    exact hMA _ (d.coordinate_mem_body (interior_subset hx))

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
