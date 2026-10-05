import GaussianTilt.MomentMapClassicalDirichletIntrinsicFlatEquation
import GaussianTilt.MomentMapLinearDirichletQuantitativeCoefficientChart

/-! # A constructed fixed chart carrying its actual quantitative geometry -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ} {S A : Set (E n)}

structure IntrinsicFixedChart (d : SmoothInnerDomain S A) (p : BoundaryChartPatch d.coordinateDefining) where
  scale : ℝ
  radius_factor : ℝ
  chart_bound : ℝ
  raw_bound : ℝ
  jacobian_bound : ℝ
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  radius_factor_pos : 0 < radius_factor
  radius_factor_le_one : radius_factor ≤ 1
  chart_bound_ge_one : 1 ≤ chart_bound
  raw_bound_ge_one : 1 ≤ raw_bound
  jacobian_bound_ge_one : 1 ≤ jacobian_bound
  inverse : ∀ z ∈ Metric.closedBall (0:E n) (2*scale),
    z ∈ (regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).target ∧
    ContDiffAt ℝ ∞ (regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).symm z ∧
    dist ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).symm z)
      (d.physicalChartCenter p) < p.radius/2 ∧
    d.defining ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).symm z)=
      d.defining (d.physicalChartCenter p)-z p.index ∧
    ThreeDerivativeBound (regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).symm z chart_bound
  forward : ∀ x ∈ Metric.closedBall (d.physicalChartCenter p) p.radius,
    ThreeDerivativeBound (flatteningMap d.defining (d.physicalChartCenter p) p.index) x chart_bound ∧
    ThreeDerivativeBound d.defining x chart_bound
  ball : ∀ z ∈ Metric.closedBall (0:E n) scale, 0 < z p.index →
    0 < radius_factor*z p.index ∧ radius_factor*z p.index ≤ 1 ∧
    Metric.closedBall ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).symm z)
      (radius_factor*z p.index) ⊆ {x | d.defining x < d.defining (d.physicalChartCenter p)} ∩
        Metric.closedBall (d.physicalChartCenter p) p.radius
  inverse_lipschitz : ∀ z ∈ Metric.closedBall (0:E n) (2*scale), ∀ z' ∈ Metric.closedBall (0:E n) (2*scale),
    dist ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).symm z)
      ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).symm z') ≤ chart_bound*dist z z'
  forward_lipschitz : ∀ x ∈ Metric.closedBall (d.physicalChartCenter p) p.radius,
    ∀ y ∈ Metric.closedBall (d.physicalChartCenter p) p.radius,
    dist (flatteningMap d.defining (d.physicalChartCenter p) p.index x)
      (flatteningMap d.defining (d.physicalChartCenter p) p.index y) ≤ chart_bound*dist x y
  raw_smooth : ∀ y, ‖(coordinateEquiv n).symm y‖ < 2 →
    ContDiffAt ℝ ∞ (d.intrinsicScaledChart p scale) y ∧
    ∀ i k, ContDiffAt ℝ ∞ (fun z => d.intrinsicScaledJacobian p scale z i k) y
  raw_derivatives : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 →
    ThreeDerivativeBound (d.intrinsicScaledChart p scale) y raw_bound ∧
    (∀ i k, |d.intrinsicScaledJacobian p scale y i k| ≤ jacobian_bound) ∧
    ∀ k i l, |matrixCoordinateDerivative (d.intrinsicScaledJacobian p scale) k y i l| ≤ jacobian_bound

namespace SmoothInnerDomain
variable (d : SmoothInnerDomain S A)

theorem exists_intrinsicFixedChart (p : BoundaryChartPatch d.coordinateDefining) :
    Nonempty (IntrinsicFixedChart d p) := by
  obtain ⟨s,c,C,hs,hs1,hc,hc1,hC,hInv,hForward,hBall,hInvLip,hForwardLip⟩ :=
    exists_quantitative_regularLevelFlattening_chart d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) p.radius_pos
  obtain ⟨Cx,Cj,hCx,hCj,hRawSmooth,hRawBound⟩ := exists_scaled_raw_chart_bounds d.smooth
    (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p) hs
    (fun z hz => (hInv z hz).2.1)
  exact ⟨⟨s,c,C,Cx,Cj,hs,hs1,hc,hc1,hC,hCx,hCj,hInv,hForward,hBall,hInvLip,hForwardLip,hRawSmooth,hRawBound⟩⟩

end SmoothInnerDomain
namespace IntrinsicFixedChart
variable {d : SmoothInnerDomain S A} {p : BoundaryChartPatch d.coordinateDefining} (c : IntrinsicFixedChart d p)

lemma scaled_mem_big_ball {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) :
    c.scale • (coordinateEquiv n).symm y ∈ Metric.closedBall (0:E n) (2*c.scale) := by
  simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg c.scale_pos.le]
  nlinarith [c.scale_pos]

lemma scaled_target {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) :
    c.scale • (coordinateEquiv n).symm y ∈
      (regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).target :=
  (c.inverse _ (c.scaled_mem_big_ball hy)).1

lemma map_patch {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) :
    d.intrinsicScaledChart p c.scale y ∈ Metric.closedBall p.center p.radius :=
  d.intrinsicScaledChart_mem_patch p c.scale y (c.inverse _ (c.scaled_mem_big_ball hy)).2.2.1

lemma level {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) :
    d.coordinateDefining (d.intrinsicScaledChart p c.scale y) = -c.scale*y p.index :=
  d.intrinsicScaledChart_level p c.scale (c.scaled_target hy)

lemma interior_ball {y : CoordinateSpace n} (hy : y ∈ flatHalfBall p.index) :
    0 < c.radius_factor*c.scale*y p.index ∧ c.radius_factor*c.scale*y p.index ≤ 1 ∧
    ∀ z, ‖(coordinateEquiv n).symm z-(coordinateEquiv n).symm (d.intrinsicScaledChart p c.scale y)‖ < c.radius_factor*c.scale*y p.index →
      z ∈ interior {x | d.coordinateDefining x ≤ 0} := by
  have hh := scaled_raw_chart_height_ball d.smooth (d.physicalChartCenter p) p.index
    (d.physicalChartCenter_transverse p) c.scale_pos c.ball hy.1.le hy.2
  refine ⟨hh.1,hh.2.1,?_⟩
  apply d.intrinsicScaledChart_ball_inside p c.scale
  intro z hz
  exact (hh.2.2 hz).1

lemma map_interior {y : CoordinateSpace n} (hy : y ∈ flatHalfBall p.index) :
    d.intrinsicScaledChart p c.scale y ∈ interior {x | d.coordinateDefining x ≤ 0} :=
  (c.interior_ball hy).2.2 _ (by simpa using (c.interior_ball hy).1)

end IntrinsicFixedChart
end GaussianTilt.MomentMapRegularity
