import GaussianTilt.MomentMapClassicalDirichletIntrinsicFlatForcing
import GaussianTilt.MomentMapLinearDirichletQuantitativeCoefficient

/-! # The actual flattened scalar PDE for intrinsic continuation jets -/
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

/-- Every coefficient and source in the actual flattened equation is
identified, including the curvature drift and its scaling factor. -/
theorem intrinsic_scaled_chart_equation {α : ℝ} (hα : 0 < α)
    (p : BoundaryChartPatch d.coordinateDefining) (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}))
    (hp : ∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef)
    (hMA : ∀ y ∈ {z | d.coordinateDefining z ≤ 0},
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y)
    {y : CoordinateSpace n}
    (hx : d.intrinsicScaledChart p s y ∈ interior {x | d.coordinateDefining x ≤ 0})
    (hxp : d.intrinsicScaledChart p s y ∈ Metric.closedBall p.center p.radius)
    (hz : s • (coordinateEquiv n).symm y ∈
      (regularLevelFlatteningChart d.smooth (d.physicalChartCenter p) p.index (d.physicalChartCenter_transverse p)).target)
    (β : CoordinateSpace n → ℝ) (hβ : ContDiff ℝ ∞ β) (a : Fin n) :
    let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
    let T := intrinsicTangentField d.coordinate_body_convex α j.1 β a p.index
    let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F β a p.index
    let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
    let X := d.intrinsicScaledChart p s
    let A := scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) s (fun x => (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹)
    linearizedMA (A y) (T ∘ X) y = flattenedTangentForcing s g b T X p.index y := by
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  let T := intrinsicTangentField d.coordinate_body_convex α j.1 β a p.index
  let X := d.intrinsicScaledChart p s
  have hMAlog (z : CoordinateSpace n) (hz : z ∈ interior {w | d.coordinateDefining w ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 z).det = Real.exp (F z) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef z))]
    exact hMA z (interior_subset hz)
  have hT : ContDiffAt ℝ 2 T (X y) := contDiffAt_infty.mp
    ((contDiffOn_intrinsicTangentField d.coordinate_body_convex hα j.1 hs hβ a p.index).contDiffAt
      (isOpen_interior.mem_nhds hx)) 2
  have hflat := linearizedMA_scaled_flattened_pullback d.smooth (d.physicalChartCenter p) p.index
    (d.physicalChartCenter_transverse p) s hz (d.intrinsicScaledChart_normal_ne_zero p s hxp) hT
    ((intrinsicHessian d.coordinate_body_convex α j.1 (X y))⁻¹)
  have heq := intrinsic_tangent_field_equation d.coordinate_body_convex hα j.1 hs hMAlog hx
    (hp _ (interior_subset hx)) (contDiff_infty.mp hβ 2).contDiffAt a p.index
  change linearizedMA (scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) s (fun x => (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹) y)
      (T ∘ X) y = _
  change linearizedMA (scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) s (fun x => (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹) y)
      (T ∘ X) y = s^2*linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 (X y))⁻¹ T (X y)+
      s*linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 (X y))⁻¹ d.coordinateDefining (X y)*
        coordinateDerivative p.index (T ∘ X) y at hflat
  rw [hflat,heq]
  rfl

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
