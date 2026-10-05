import GaussianTilt.MomentMapClassicalDirichletBoundaryCharts

/-! # Finite genuine boundary chart coverage -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Actual compact chart data, constructed from the defining function. -/
structure BoundaryChartPatch (w : CoordinateSpace n → ℝ) where
  center : CoordinateSpace n
  index : Fin n
  radius : ℝ
  radius_pos : 0 < radius
  level_zero : w center = 0
  denominator : ℝ
  denominator_pos : 0 < denominator
  bound₀ : ℝ
  bound₁ : ℝ
  bound₂ : ℝ
  bound₀_nonneg : 0 ≤ bound₀
  bound₁_nonneg : 0 ≤ bound₁
  bound₂_nonneg : 0 ≤ bound₂
  denominator_bound : ∀ y ∈ Metric.closedBall center radius, denominator ≤ |coordinateDerivative index w y|
  smooth : ∀ y ∈ Metric.closedBall center radius, ∀ a,
    ContDiffAt ℝ ∞ (boundaryChartCoefficient w index a) y
  value_bound : ∀ y ∈ Metric.closedBall center radius, ∀ a,
    |boundaryChartCoefficient w index a y| ≤ bound₀
  derivative_bound : ∀ y ∈ Metric.closedBall center radius, ∀ a i,
    |coordinateDerivative i (boundaryChartCoefficient w index a) y| ≤ bound₁
  hessian_bound : ∀ y ∈ Metric.closedBall center radius, ∀ a i j,
    |coordinateHessian (boundaryChartCoefficient w index a) y i j| ≤ bound₂

lemma exists_boundaryChartPatch {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    {x : CoordinateSpace n} (hx : w x = 0) (hg : coordinateGradient w x ≠ 0) :
    ∃ p : BoundaryChartPatch w, p.center = x := by
  have hj : ∃ j : Fin n, coordinateDerivative j w x ≠ 0 := by
    by_contra! hz
    exact hg (funext hz)
  obtain ⟨j,hj⟩ := hj
  obtain ⟨r,c,M₀,M₁,M₂,hr,hc,hM₀,hM₁,hM₂,hden,hs,hb₀,hb₁,hb₂⟩ := exists_boundary_chart_bounds hw hj
  exact ⟨⟨x,j,r,hr,hx,c,hc,M₀,M₁,M₂,hM₀,hM₁,hM₂,hden,hs,hb₀,hb₁,hb₂⟩,rfl⟩

namespace BoundaryChartPatch
variable {w : CoordinateSpace n → ℝ} (p : BoundaryChartPatch w)

lemma derivative_ne_zero {y : CoordinateSpace n} (hy : y ∈ Metric.closedBall p.center p.radius) :
    coordinateDerivative p.index w y ≠ 0 :=
  abs_pos.mp (p.denominator_pos.trans_le (p.denominator_bound y hy))

lemma tangent_field_vanishes {u : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    {y : CoordinateSpace n} (hy : y ∈ Metric.closedBall p.center p.radius)
    (hu : DifferentiableAt ℝ u y)
    (hzero : ∀ᶠ z in 𝓝 y, w z = w y → u z = u y) (a : Fin n) :
    coordinateDerivative a u y - boundaryChartCoefficient w p.index a y * coordinateDerivative p.index u y = 0 :=
  boundary_tangential_field_eq_zero hu (contDiff_infty.mp hw 2).contDiffAt
    (p.derivative_ne_zero hy) hzero a

end BoundaryChartPatch

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Compactness supplies finitely many true chart patches; the smaller
half-radius balls cover the entire boundary, leaving room for barriers. -/
theorem exists_finite_coordinate_boundary_atlas :
    ∃ P : Finset (BoundaryChartPatch d.coordinateDefining),
      frontier {x | d.coordinateDefining x ≤ 0} ⊆
        ⋃ p ∈ P, Metric.ball p.center (p.radius/2) := by
  classical
  let B := frontier {x | d.coordinateDefining x ≤ 0}
  have hB : IsCompact B := d.coordinate_body_compact.of_isClosed_subset isClosed_frontier
    (by rw [← d.coordinate_body_compact.isClosed.closure_eq]; exact frontier_subset_closure)
  have hp : ∀ x : B, ∃ p : BoundaryChartPatch d.coordinateDefining, p.center = x := by
    intro x
    have hx : d.coordinateDefining x = 0 := d.coordinate_zero_boundary x x.property
    exact exists_boundaryChartPatch d.coordinateDefining_smooth hx (d.coordinate_gradient_ne_zero hx)
  choose p hp using hp
  have hcover : B ⊆ ⋃ x : B, Metric.ball (p x).center ((p x).radius/2) := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x,hx⟩, ?_⟩
    rw [hp]
    exact Metric.mem_ball_self (half_pos (p ⟨x,hx⟩).radius_pos)
  obtain ⟨F,hF⟩ := hB.elim_finite_subcover
    (fun x : B => Metric.ball (p x).center ((p x).radius/2))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨F.image p, ?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hF hx)
  exact mem_iUnion₂.mpr ⟨p y, Finset.mem_image.mpr ⟨y,hy,rfl⟩, hxy⟩

lemma tangent_field_zero_on_coordinate_boundary {u : CoordinateSpace n → ℝ}
    (p : BoundaryChartPatch d.coordinateDefining) {y : CoordinateSpace n}
    (hyp : y ∈ Metric.closedBall p.center p.radius)
    (hy : y ∈ frontier {x | d.coordinateDefining x ≤ 0})
    (hu : DifferentiableAt ℝ u y)
    (hzero : ∀ z ∈ frontier {x | d.coordinateDefining x ≤ 0}, u z = 0) (a : Fin n) :
    coordinateDerivative a u y - boundaryChartCoefficient d.coordinateDefining p.index a y *
      coordinateDerivative p.index u y = 0 := by
  apply p.tangent_field_vanishes d.coordinateDefining_smooth hyp hu
  apply Eventually.of_forall
  intro z hz
  have hzb : z ∈ frontier {x | d.coordinateDefining x ≤ 0} := by
    rw [d.coordinate_body_frontier]
    exact hz.trans (d.coordinate_zero_boundary y hy)
  rw [hzero z hzb,hzero y hy]

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
