import GaussianTilt.MomentMapClassicalDirichletFixedChart
import GaussianTilt.MomentMapClassicalDirichletIntrinsicSmoothness

/-! # Genuine flat elliptic systems constructed from the actual Monge--Ampère jets -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ} {S A : Set (E n)}
namespace IntrinsicFixedChart
variable {d : SmoothInnerDomain S A} {p : BoundaryChartPatch d.coordinateDefining} (c : IntrinsicFixedChart d p)

/-- A positive solution of the genuine Banach-jet equation supplies every
hypothesis of the proved noncircular flat boundary estimate. All constants
precede the unknown solution, and interior smoothness is now derived. -/
theorem exists_intrinsic_flat_system [NeZero n] {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ lam Λ K M B : ℝ,
      0 < lam ∧ 0 < Λ ∧ 0 ≤ K ∧ 0 ≤ M ∧ 0 ≤ B ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ a,
      let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
      let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
      let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
      let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
      let X := d.intrinsicScaledChart p c.scale
      let D := fun y => (intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index (X y)).comp (fderiv ℝ X y)
      let Ac := scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
        (d.physicalChartCenter_transverse p) c.scale (fun x => (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹)
      LocalFlatEllipticSystem p.index (T ∘ X) (flattenedTangentForcing c.scale g b T X p.index) Ac lam Λ K M ∧
      FlatScalarData p.index (T ∘ X) (flattenedTangentForcing c.scale g b T X p.index) D M B := by
  obtain ⟨β,M,B,hM,hB,hβ,heβ,hscalar⟩ := d.intrinsic_flat_scalar_data hα p
    c.scale_pos c.scale_le_one c.radius_factor_pos (zero_le_one.trans c.raw_bound_ge_one)
    (fun y hy => (c.raw_smooth y (by linarith)).1)
    (fun y hy => ⟨(c.raw_derivatives y hy).1.1,(c.raw_derivatives y hy).1.2.1⟩)
    (fun y hy => c.map_patch hy) (fun y hy => c.level hy)
    (fun y hy => ⟨(c.interior_ball hy).2.1,(c.interior_ball hy).2.2⟩)
  obtain ⟨lam,Λ,hlam,hΛ,hEll⟩ := d.intrinsic_dirichletContinuation_uniform_inverse_ellipticity hα
  obtain ⟨K,hK,hDA⟩ := d.intrinsic_dirichletContinuation_scaled_inverse_derivative_bound hα
  let Q := (n:ℝ)^2*c.chart_bound^2
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hCpos : 0 < c.chart_bound := zero_lt_one.trans_le c.chart_bound_ge_one
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let Kc := (n:ℝ)^2*c.jacobian_bound^2*(2*Λ+(n:ℝ)*K*c.raw_bound/(c.radius_factor*c.scale))
  have hKc : 0 ≤ Kc := by
    dsimp [Kc]
    have hCx := c.raw_bound_ge_one
    have hc := c.radius_factor_pos
    have hs := c.scale_pos
    positivity
  refine ⟨β,lam/Q,Λ*Q,Kc,M,B,div_pos hlam hQ,mul_pos hΛ hQ,hKc,hM,hB,hβ,heβ,?_⟩
  intro t ht j hp hMA a
  have hs := d.intrinsic_dirichletContinuation_interior_smooth hα hα1 ht j hp hMA
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
  let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
  let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
  let X := d.intrinsicScaledChart p c.scale
  let Ac := scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
    (d.physicalChartCenter_transverse p) c.scale (fun x => (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹)
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (z : CoordinateSpace n) (hz : z ∈ interior {w | d.coordinateDefining w ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 z).det = Real.exp (F z) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef z))]
    exact hMA z (interior_subset hz)
  have hAs (i l : Fin n) := contDiffOn_intrinsicInverseHessian d.coordinate_body_convex hα j.1 hs hF hMAlog i l
  have hcBounds (y : CoordinateSpace n) (hy : y ∈ flatHalfBall p.index) :
      (Ac y).PosDef ∧ (∀ v : CoordinateSpace n,
        (lam/Q)*‖(coordinateEquiv n).symm v‖^2 ≤ v ⬝ᵥ (Ac y *ᵥ v) ∧
        v ⬝ᵥ (Ac y *ᵥ v) ≤ (Λ*Q)*‖(coordinateEquiv n).symm v‖^2) ∧
      ∀ k i l, y p.index*|matrixCoordinateDerivative Ac k y i l| ≤ Kc := by
    apply scaled_raw_chart_coefficient_bounds d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) (Nat.pos_of_ne_zero (NeZero.ne n))
      c.scale_pos c.radius_factor_pos c.chart_bound_ge_one c.raw_bound_ge_one c.jacobian_bound_ge_one
      p.radius_pos hlam.le hΛ.le hK c.inverse c.forward c.raw_smooth c.raw_derivatives hy.1.le hy.2
    · exact (hp _ (interior_subset (c.map_interior hy))).inv
    · intro i l
      exact ((hAs i l).contDiffAt (isOpen_interior.mem_nhds (c.map_interior hy))).differentiableAt (by simp)
    · intro v
      have hh := hEll t ht j hs hp hMA (X y) (interior_subset (c.map_interior hy)) v
      simpa only [coordinateEuclidean_norm_sq] using hh
    · intro k i l
      exact hDA t ht j hs hp hMA (X y) (c.radius_factor*c.scale*y p.index)
        (c.interior_ball hy).1 (c.interior_ball hy).2.1 (c.interior_ball hy).2.2 k i l
  have hsd := hscalar t ht j hs hp hMA a
  refine ⟨⟨hsd.continuous,hsd.smooth,hsd.forcing_smooth,?_,
    fun y hy => (hcBounds y hy).1,fun y hy => (hcBounds y hy).2.1,
    fun y hy => (hcBounds y hy).2.2,hsd.forcing_bound,hsd.forcing_derivative_bound,?_⟩,hsd⟩
  · intro i l y hy
    have hraw := c.raw_smooth y (by linarith [hy.1])
    exact (contDiffAt_scaledRawChartCoefficient d.smooth (d.physicalChartCenter p) p.index
      (d.physicalChartCenter_transverse p) c.scale hraw.1 hraw.2
      (fun k m => (hAs k m).contDiffAt (isOpen_interior.mem_nhds (c.map_interior hy))) i l).contDiffWithinAt
  · intro y hy
    exact d.intrinsic_scaled_chart_equation hα p c.scale ht j hs hp hMA
      (c.map_interior hy) (c.map_patch hy.1.le) (c.scaled_target hy.1.le) (β a) (hβ a) a

end IntrinsicFixedChart
end GaussianTilt.MomentMapRegularity
