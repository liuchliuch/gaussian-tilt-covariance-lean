import GaussianTilt.MomentMapClassicalDirichletChartWithinData
import GaussianTilt.MomentMapLinearDirichletQuantitativeChartRaw

/-! # The genuine fixed flattening chart specialized to the constructed domain -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

def physicalChartCenter (p : BoundaryChartPatch d.coordinateDefining) : E n :=
  (coordinateEquiv n).symm p.center

lemma physicalChartCenter_level (p : BoundaryChartPatch d.coordinateDefining) :
    d.defining (d.physicalChartCenter p) = 0 := p.level_zero

lemma physicalChartCenter_transverse (p : BoundaryChartPatch d.coordinateDefining) :
    fderiv ℝ d.defining (d.physicalChartCenter p) (EuclideanSpace.basisFun (Fin n) ℝ p.index) ≠ 0 := by
  have hh := coordinateDerivative_pullback_at (d.smooth.differentiable (by simp) (d.physicalChartCenter p)) p.index
  rw [← hh]
  change coordinateDerivative p.index d.coordinateDefining (coordinateEquiv n ((coordinateEquiv n).symm p.center)) ≠ 0
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact p.derivative_ne_zero (Metric.mem_closedBall_self p.radius_pos.le)

def intrinsicScaledChart (p : BoundaryChartPatch d.coordinateDefining) (s : ℝ) : CoordinateSpace n → CoordinateSpace n :=
  scaledRawInverseChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p) s

def intrinsicScaledJacobian (p : BoundaryChartPatch d.coordinateDefining) (s : ℝ) :
    CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ :=
  scaledRawChartJacobian d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p) s

lemma intrinsicScaledChart_mem_patch (p : BoundaryChartPatch d.coordinateDefining) (s : ℝ)
    (y : CoordinateSpace n)
    (hclose : dist ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p)).symm (s • (coordinateEquiv n).symm y))
      (d.physicalChartCenter p) < p.radius/2) :
    d.intrinsicScaledChart p s y ∈ Metric.closedBall p.center p.radius := by
  apply (coordinate_dist_le_euclidean_dist (d.intrinsicScaledChart p s y) p.center).trans
  change ‖(coordinateEquiv n).symm (d.intrinsicScaledChart p s y)-(coordinateEquiv n).symm p.center‖ ≤ p.radius
  simp only [intrinsicScaledChart,scaledRawInverseChart,ContinuousLinearEquiv.symm_apply_apply]
  change dist _ (d.physicalChartCenter p) ≤ p.radius
  linarith [p.radius_pos]

lemma intrinsicScaledChart_level (p : BoundaryChartPatch d.coordinateDefining) (s : ℝ)
    {y : CoordinateSpace n}
    (hz : s • (coordinateEquiv n).symm y ∈
      (regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).target) :
    d.coordinateDefining (d.intrinsicScaledChart p s y) = -s*y p.index := by
  have hh := regularLevelFlatteningChart_inverse_level d.smooth (d.physicalChartCenter p) p.index
    (d.physicalChartCenter_transverse p) hz
  simp only [d.physicalChartCenter_level,PiLp.smul_apply,smul_eq_mul,zero_sub] at hh
  simpa only [coordinateDefining,coordinatePullback,Function.comp_apply,intrinsicScaledChart,
    scaledRawInverseChart,ContinuousLinearEquiv.symm_apply_apply,neg_mul] using hh

lemma intrinsicScaledChart_normal_ne_zero (p : BoundaryChartPatch d.coordinateDefining) (s : ℝ)
    {y : CoordinateSpace n} (hx : d.intrinsicScaledChart p s y ∈ Metric.closedBall p.center p.radius) :
    fderiv ℝ d.defining ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p)).symm (s • (coordinateEquiv n).symm y))
      (EuclideanSpace.basisFun (Fin n) ℝ p.index) ≠ 0 := by
  have hh := coordinateDerivative_pullback_at
    (d.smooth.differentiable (by simp) ((coordinateEquiv n).symm (d.intrinsicScaledChart p s y))) p.index
  have hp := p.derivative_ne_zero hx
  rw [← coordinateDefining,ContinuousLinearEquiv.apply_symm_apply] at hh
  rw [hh] at hp
  simpa only [intrinsicScaledChart,scaledRawInverseChart,ContinuousLinearEquiv.symm_apply_apply] using hp

lemma intrinsicScaledChart_ball_inside (p : BoundaryChartPatch d.coordinateDefining) (s : ℝ)
    {y : CoordinateSpace n} {r : ℝ}
    (hball : Metric.closedBall
      ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index
        (d.physicalChartCenter_transverse p)).symm (s • (coordinateEquiv n).symm y)) r ⊆
      {x | d.defining x < d.defining (d.physicalChartCenter p)}) :
    ∀ z, ‖(coordinateEquiv n).symm z-(coordinateEquiv n).symm (d.intrinsicScaledChart p s y)‖ < r →
      z ∈ interior {x | d.coordinateDefining x ≤ 0} := by
  intro z hz
  rw [d.coordinate_body_interior]
  have hh := hball (show (coordinateEquiv n).symm z ∈ Metric.closedBall
      ((regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index
        (d.physicalChartCenter_transverse p)).symm (s • (coordinateEquiv n).symm y)) r from by
    simpa only [intrinsicScaledChart,scaledRawInverseChart,ContinuousLinearEquiv.symm_apply_apply,
      Metric.mem_closedBall,dist_eq_norm] using hz.le)
  simpa only [d.physicalChartCenter_level] using hh

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
