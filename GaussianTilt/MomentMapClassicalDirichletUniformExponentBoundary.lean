import GaussianTilt.MomentMapBoundaryRegularityChartPullback
import GaussianTilt.MomentMapClassicalDirichletUniformExponentRecovery
import GaussianTilt.MomentMapClassicalDirichletIntrinsicHessianRecovery

/-! # Uniform actual tangential and Hessian approach on each intrinsic chart -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ} {S A : Set (E n)}
namespace IntrinsicFixedChart
variable {d : SmoothInnerDomain S A} {p : BoundaryChartPatch d.coordinateDefining} (c : IntrinsicFixedChart d p)
include c

theorem exists_intrinsic_tangent_derivative_approach_all_exponents [NeZero n] :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ γ r L : ℝ,
      0 < γ ∧ γ ≤ 1 ∧ 0 < r ∧ r ≤ 1 ∧ 2*r ≤ p.radius ∧ 0 ≤ L ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ (α : ℝ), 0 < α → α < 1 → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ u : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α u.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α u.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ z ∈ Metric.ball (d.physicalChartCenter p) r, d.defining z=0 →
      ∀ x, d.defining x ≤ 0 → dist x z ≤ r → ∀ a k,
        |intrinsicTangentDifferential d.coordinate_body_convex α u.1 (β a) a p.index (coordinateEquiv n x) (Pi.single k 1)-
          intrinsicTangentDifferential d.coordinate_body_convex α u.1 (β a) a p.index (coordinateEquiv n z) (Pi.single k 1)| ≤
          L*(dist x z)^γ := by
  obtain ⟨β,lam,Λ,K,M,B,hlam,hΛ,hK,hM,hB,hβ,heβ,hsystem⟩ := c.exists_intrinsic_flat_system_all_exponents
  obtain ⟨γ,r,C,hγ,hγ1,hr,hr1,hrρ,hC,hpull⟩ :=
    exists_chart_derivative_holder_all_boundary_centers d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) c.scale_pos p.radius_pos hlam hΛ.le hK
      (fun y hy => (c.raw_smooth y (by linarith)).1)
  refine ⟨β,γ,r,C*(B+M),hγ,hγ1,hr,hr1,hrρ,by positivity,hβ,heβ,?_⟩
  intro α hα hα1 t ht u hp hMA z hz hwz x hwx hxz a k
  have hd := hsystem α hα hα1 t ht u hp hMA a
  exact hpull _ _ _ _ M B hM hB hd.1 hd.2.derivative_continuous hd.2.derivative
    hd.2.derivative_bound hd.2.boundary_zero z hz (by simpa only [d.physicalChartCenter_level] using hwz)
    x (by simpa only [d.physicalChartCenter_level] using hwx) hxz k

/-- Full Hessian approach at every boundary center in the smaller actual
chart. Both tangential regularity and the nonlinear normal recovery are
proved, and all constants are fixed before the homotopy solution. -/
theorem exists_intrinsic_hessian_boundary_approach_all_exponents [NeZero n] :
    ∃ γ r C : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < r ∧ r ≤ 1 ∧ 2*r ≤ p.radius ∧ 0 ≤ C ∧
      ∀ (α : ℝ), 0 < α → α < 1 → ∀ t ∈ Icc (0:ℝ) 1,
      ∀ u : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α u.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α u.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ z ∈ Metric.ball (d.physicalChartCenter p) r, d.defining z=0 →
      ∀ x, d.defining x ≤ 0 → dist x z ≤ r → ∀ i l,
        |intrinsicHessian d.coordinate_body_convex α u.1 (coordinateEquiv n x) i l-
          intrinsicHessian d.coordinate_body_convex α u.1 (coordinateEquiv n z) i l| ≤ C*(dist x z)^γ := by
  obtain ⟨β,γ,r,L,hγ,hγ1,hr,hr1,hrρ,hL,hβ,heβ,hT⟩ := c.exists_intrinsic_tangent_derivative_approach_all_exponents
  obtain ⟨C,hC,hrec⟩ := d.intrinsic_hessian_approach_of_tangent_derivative_approach_all_exponents p
  refine ⟨γ,r,C*(1+L),hγ,hγ1,hr,hr1,hrρ,by positivity,?_⟩
  intro α hα hα1 t ht u hp hMA z hz hwz x hwx hxz i l
  have hzdist : dist z (d.physicalChartCenter p) < r := hz
  have hxdist : dist x (d.physicalChartCenter p) ≤ 2*r := by linarith [dist_triangle x z (d.physicalChartCenter p)]
  have norm_raw_le_physical (v : E n) : ‖coordinateEquiv n v‖ ≤ ‖v‖ := by
    apply pi_norm_le_iff_of_nonneg (norm_nonneg v) |>.mpr
    intro k
    exact PiLp.norm_apply_le v k
  have hxpatch : coordinateEquiv n x ∈ Metric.closedBall p.center p.radius := by
    change ‖coordinateEquiv n x-p.center‖ ≤ p.radius
    have he : p.center=coordinateEquiv n (d.physicalChartCenter p) := by simp [SmoothInnerDomain.physicalChartCenter]
    rw [he,← map_sub]
    exact (norm_raw_le_physical _).trans (by simpa only [dist_eq_norm] using hxdist.trans hrρ)
  have hzpatch : coordinateEquiv n z ∈ Metric.closedBall p.center p.radius := by
    change ‖coordinateEquiv n z-p.center‖ ≤ p.radius
    have he : p.center=coordinateEquiv n (d.physicalChartCenter p) := by simp [SmoothInnerDomain.physicalChartCenter]
    rw [he,← map_sub]
    exact (norm_raw_le_physical _).trans (by rw [← dist_eq_norm]; linarith)
  have hh := hrec α hα hα1 γ L hγ1 hL t ht u hp hMA β hβ heβ
    (coordinateEquiv n x) hxpatch (by simpa only [SmoothInnerDomain.coordinateDefining,coordinatePullback,ContinuousLinearEquiv.symm_apply_apply] using hwx)
    (coordinateEquiv n z) hzpatch (by change d.defining z ≤ 0; exact hwz.le)
    (by simpa only [ContinuousLinearEquiv.symm_apply_apply,← dist_eq_norm] using hxz.trans hr1)
    (by simpa only [ContinuousLinearEquiv.symm_apply_apply,← dist_eq_norm] using hT α hα hα1 t ht u hp hMA z hz hwz x hwx hxz) i l
  simpa only [ContinuousLinearEquiv.symm_apply_apply,← dist_eq_norm] using hh

end IntrinsicFixedChart
end GaussianTilt.MomentMapRegularity
