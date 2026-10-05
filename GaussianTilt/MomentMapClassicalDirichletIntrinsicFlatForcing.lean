import GaussianTilt.MomentMapClassicalDirichletIntrinsicChartGeometry
import GaussianTilt.MomentMapBoundaryRegularityZeroBoundary

/-! # Actual scalar forcing and intrinsic boundary derivatives after flattening -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

structure FlatScalarData (q : Fin n) (u f : CoordinateSpace n → ℝ)
    (D : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ) (M B : ℝ) : Prop where
  continuous : ContinuousOn u (flatClosedHalfBall q)
  smooth : ContDiffOn ℝ ∞ u (flatHalfBall q)
  forcing_smooth : ContDiffOn ℝ ∞ f (flatHalfBall q)
  derivative_continuous : ContinuousOn D (flatClosedHalfBall q)
  derivative : ∀ y ∈ flatClosedHalfBall q, HasFDerivWithinAt u (D y) (flatClosedHalfBall q) y
  derivative_bound : ∀ y ∈ flatClosedHalfBall q, ‖D y‖ ≤ B
  boundary_zero : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → y q=0 → u y=0
  forcing_bound : ∀ y ∈ flatHalfBall q, |f y| ≤ M
  forcing_derivative_bound : ∀ y ∈ flatHalfBall q, ∀ k, y q*|coordinateDerivative k f y| ≤ M

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The actual intrinsic chart fields satisfy all scalar hypotheses of
the flat boundary estimate, including the full curvature forcing. Only
fixed chart geometry is supplied, and no scalar estimate is a premise. -/
theorem intrinsic_flat_scalar_data [NeZero n] {α : ℝ} (hα : 0 < α)
    (p : BoundaryChartPatch d.coordinateDefining)
    {s c Cx : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hc : 0 < c) (hCx : 0 ≤ Cx)
    (hXs : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → ContDiffAt ℝ ∞ (d.intrinsicScaledChart p s) y)
    (hXb : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 →
      ‖fderiv ℝ (d.intrinsicScaledChart p s) y‖ ≤ Cx ∧
      ‖fderiv ℝ (fderiv ℝ (d.intrinsicScaledChart p s)) y‖ ≤ Cx)
    (hXp : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → d.intrinsicScaledChart p s y ∈ Metric.closedBall p.center p.radius)
    (hXlevel : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 →
      d.coordinateDefining (d.intrinsicScaledChart p s y) = -s*y p.index)
    (hBall : ∀ y ∈ flatHalfBall p.index, c*s*y p.index ≤ 1 ∧
      ∀ z, ‖(coordinateEquiv n).symm z-(coordinateEquiv n).symm (d.intrinsicScaledChart p s y)‖ < c*s*y p.index →
        z ∈ interior {x | d.coordinateDefining x ≤ 0}) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ a,
      let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
      let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
      let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
      let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
      let X := d.intrinsicScaledChart p s
      let D := fun y => (intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index (X y)).comp (fderiv ℝ X y)
      FlatScalarData p.index (T ∘ X) (flattenedTangentForcing s g b T X p.index) D M B := by
  obtain ⟨β,N,hN,hβ,heβ,hscalar⟩ := d.intrinsic_dirichletContinuation_chart_scalar_bounds hα p
  obtain ⟨Cw,hCw,hwithin⟩ := d.intrinsic_dirichletContinuation_chart_within_bounds hα p
  let M₀ := N+N*((n:ℝ)*N*Cx)
  let M₁ := (n:ℝ)*N*Cx+((n:ℝ)*N*Cx)*((n:ℝ)*N*Cx)+N*((n:ℝ)^2*N*Cx^2+(n:ℝ)*N*Cx)
  let M := max (max M₀ (M₁/(c*s))) 0
  refine ⟨β,M,Cw*Cx,le_max_right _ _,mul_nonneg hCw hCx,hβ,heβ,?_⟩
  intro t ht j hsm hp hMA a
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  let T := intrinsicTangentField d.coordinate_body_convex α j.1 (β a) a p.index
  let g := intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index
  let b := fun x => linearizedMA (intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ d.coordinateDefining x
  let X := d.intrinsicScaledChart p s
  let D := fun y => (intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index (X y)).comp (fderiv ℝ X y)
  have hXmap : MapsTo X (flatClosedHalfBall p.index) {x | d.coordinateDefining x ≤ 0} := by
    intro y hy
    change d.coordinateDefining (X y) ≤ 0
    rw [hXlevel y hy.1]
    nlinarith [hy.2]
  have hXi (y : CoordinateSpace n) (hy : y ∈ flatHalfBall p.index) :
      X y ∈ interior {x | d.coordinateDefining x ≤ 0} := by
    rw [d.coordinate_body_interior]
    change d.coordinateDefining (X y) < 0
    rw [hXlevel y hy.1.le]
    nlinarith [hy.2]
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y (interior_subset hy)
  have hTc := continuousOn_intrinsicTangentField d.coordinate_body_convex α j.1 (hβ a).continuous.continuousOn a p.index
  have hTs := contDiffOn_intrinsicTangentField d.coordinate_body_convex hα j.1 hsm (hβ a) a p.index
  have hgs := contDiffOn_intrinsicTangentSource d.coordinate_body_convex hα j.1 hsm hF (hβ a) hMAlog a p.index
  have hbs := contDiffOn_intrinsicCurvature d.coordinate_body_convex hα j.1 hsm hF d.coordinateDefining_smooth hMAlog
  have hXc : ContinuousOn X (flatClosedHalfBall p.index) := fun y hy => (hXs y hy.1).continuousAt.continuousWithinAt
  have hDXc : ContinuousOn (fderiv ℝ X) (flatClosedHalfBall p.index) := by
    intro y hy
    exact ((hXs y hy.1).fderiv_right (m:=0) (by simp)).continuousAt.continuousWithinAt
  have hDb (y : CoordinateSpace n) (hy : y ∈ flatClosedHalfBall p.index) : ‖D y‖ ≤ Cw*Cx := by
    have hh := (hwithin t ht j hsm hp hMA (X y) (hXp y hy.1) (hXmap hy) a (β a) (heβ _ (hXp y hy.1) a)).2
    exact ((intrinsicTangentDifferential d.coordinate_body_convex α j.1 (β a) a p.index (X y)).opNorm_comp_le _).trans
      (mul_le_mul hh (hXb y hy.1).1 (norm_nonneg _) hCw)
  have hforce (y : CoordinateSpace n) (hy : y ∈ flatHalfBall p.index) :
      |flattenedTangentForcing s g b T X p.index y| ≤ M ∧
      ∀ k, y p.index*|coordinateDerivative k (flattenedTangentForcing s g b T X p.index) y| ≤ M := by
    have hr : 0 < c*s*y p.index := mul_pos (mul_pos hc hs) hy.2
    have hdata := hscalar t ht j hsm hp hMA (X y) (hXp y hy.1.le) (c*s*y p.index) hr
      (hBall y hy).1 (hBall y hy).2 a
    have hh := flattenedTangentForcing_bounds hs.le hs1
      ((hgs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))).differentiableAt (by simp))
      ((hbs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))).differentiableAt (by simp))
      (contDiffAt_infty.mp (hTs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))) 2)
      (contDiffAt_infty.mp (hXs y hy.1.le) 2) hr (hBall y hy).1 hN hN hN hN hCx
      hdata.2.2.2.1 hdata.2.2.2.2.2.1 hdata.2.2.2.2.1 hdata.2.2.2.2.2.2
      hdata.2.1 hdata.2.2.1 (hXb y hy.1.le).1 (hXb y hy.1.le).2 p.index
    refine ⟨hh.1.trans ((le_max_left M₀ (M₁/(c*s))).trans (le_max_left _ _)),?_⟩
    intro k
    have hbnd : y p.index*|coordinateDerivative k (flattenedTangentForcing s g b T X p.index) y| ≤ M₁/(c*s) := by
      apply (le_div_iff₀ (mul_pos hc hs)).mpr
      have hh' := hh.2 k
      dsimp [M₁]
      nlinarith
    exact hbnd.trans ((le_max_right M₀ (M₁/(c*s))).trans (le_max_left _ _))
  refine ⟨hTc.comp hXc hXmap,?_,?_,?_,?_,hDb,?_,fun y hy => (hforce y hy).1,fun y hy => (hforce y hy).2⟩
  · intro y hy
    exact ((hTs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))).comp y (hXs y hy.1.le)).contDiffWithinAt
  · intro y hy
    exact (contDiffAt_flattenedTangentForcing s
      (hgs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy)))
      (hbs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy)))
      (hTs.contDiffAt (isOpen_interior.mem_nhds (hXi y hy))) (hXs y hy.1.le) p.index).contDiffWithinAt
  · exact ((continuousOn_intrinsicTangentDifferential d.coordinate_body_convex α j.1 (hβ a) a p.index).comp hXc hXmap).clm_comp hDXc
  · intro y hy
    exact (intrinsicTangentField_hasFDerivWithinAt d.coordinate_body_convex hα j.1 (hXmap hy)
      ((hβ a).differentiable (by simp) _) a p.index).comp y
      ((hXs y hy.1).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt hXmap
  · intro y hy hyq
    have hx0 : d.coordinateDefining (X y)=0 := by rw [hXlevel y hy,hyq,mul_zero]
    obtain ⟨a₀,b₀,ha₀,hb₀,hab⟩ := d.intrinsic_dirichletContinuation_scaled_barriers hα
    have hbarr := hab t ht j (fun x hx => hp x (interior_subset hx))
      (fun x hx => hMA x (interior_subset hx))
    have he := (intrinsicTangentField_congr_nhds_beta d.coordinate_body_convex α j.1 (heβ _ (hXp y hy) a) a p.index).self_of_nhds
    exact he.trans (d.intrinsic_tangent_field_zero hα j p (hXp y hy) hx0 hbarr a)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
