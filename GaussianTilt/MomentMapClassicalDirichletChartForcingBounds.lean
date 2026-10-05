import GaussianTilt.MomentMapClassicalDirichletTangentialForcingBounds
import GaussianTilt.MomentMapClassicalDirichletLocalExtension

/-! # Constructed parameter-uniform chart forcing and its scaled derivative -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Genuine global smooth chart representatives and their actual forcing
bounds, uniform over solutions, parameters and interior scales r≤1. -/
theorem dirichletContinuation_chart_forcing_bounds [NeZero n]
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
        ContDiff ℝ ∞ u →
        (∀ y ∈ interior {z | d.coordinateDefining z ≤ 0}, (coordinateHessian u y).PosDef) →
        (∀ y ∈ frontier {z | d.coordinateDefining z ≤ 0}, u y = 0) →
        (∀ y ∈ interior {z | d.coordinateDefining z ≤ 0},
          (coordinateHessian u y).det = dirichletContinuationDensity d.coordinateDefining t y) →
        ∀ x ∈ Metric.closedBall p.center p.radius, ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
          y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ a,
        let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
        let B := variableInverseHessian u F
        |tangentialFieldForcing B u F (β a) a p.index x| ≤ C ∧
        ∀ k, r*|coordinateDerivative k (tangentialFieldForcing B u F (β a) a p.index) x| ≤ C := by
  obtain ⟨β,B₃,hB₃,hβs,heβ,hβ3⟩ := p.exists_smooth_chart_representatives_with_third_bound d.coordinateDefining_smooth
  obtain ⟨G,hG,hgrad⟩ := d.dirichletContinuation_uniform_coordinate_gradient
  obtain ⟨H,hH,hHess⟩ := d.dirichletContinuation_uniform_hessian
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₁,hK₁,hF₁⟩ := dirichletContinuationDensity_uniform_log_coordinateDerivative d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₂,hK₂,hF₂⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨Cₐ,hCₐ,hDA⟩ := d.dirichletContinuation_scaled_inverse_derivative_bound
  let I := ((n.factorial:ℝ)*(max H 1)^n)/c
  have hI : 0 ≤ I := by dsimp [I]; positivity
  let C₀ := K₁+p.bound₀*K₁+G*((n:ℝ)^2*I*p.bound₂)+2*p.bound₁
  let C₁ := K₂+p.bound₁*K₁+p.bound₀*K₂+H*((n:ℝ)^2*I*p.bound₂)+
    G*((n:ℝ)^2*(Cₐ*p.bound₂+I*B₃))+2*p.bound₂
  let C := max (max C₀ C₁) 0
  refine ⟨β,C,le_max_right _ _,hβs,heβ,?_⟩
  intro t ht u hu huH hub hMA x hxp r hr hr1 hball a
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  let B := variableInverseHessian u F
  have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
  have hxs := interior_subset hx
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (coordinateHessian u y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y hy
  have hnear : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact hMAlog y hy
  have hBval : B x = (coordinateHessian u x)⁻¹ := variableInverseHessian_eq_inverse (hMAlog x hx)
  have hInv : ∀ i j, |B x i j| ≤ I := by
    rw [hBval]
    exact inverse_entry_bound_of_det_lower hc (by rw [hMA x hx]; exact (hdens t ht x hxs).1)
      (hHess t ht u hu huH hub hMA x hxs)
  have hDB (k i j : Fin n) : r*|matrixCoordinateDerivative B k x i j| ≤ Cₐ := by
    have he : (fun y => B y i j) =ᶠ[𝓝 x] (fun y => (coordinateHessian u y)⁻¹ i j) :=
      hnear.mono (fun y hy => congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
        (variableInverseHessian_eq_inverse hy))
    change r*|coordinateDerivative k (fun y => B y i j) x| ≤ Cₐ
    rw [coordinateDerivative_congr_nhds he]
    exact hDA t ht u hu huH hub hMA x r hr hr1 hball k i j
  have hβ0 : |β a x| ≤ p.bound₀ := by rw [(heβ x hxp a).self_of_nhds]; exact p.value_bound x hxp a
  have hβ1 (k : Fin n) : |coordinateDerivative k (β a) x| ≤ p.bound₁ := by
    rw [coordinateDerivative_congr_nhds (heβ x hxp a)]
    exact p.derivative_bound x hxp a k
  have hβ2 (i j : Fin n) : |coordinateHessian (β a) x i j| ≤ p.bound₂ := by
    rw [coordinateHessian_congr_nhds (heβ x hxp a)]
    exact p.hessian_bound x hxp a i j
  constructor
  · have hh := tangentialFieldForcing_abs_bound x a p.index hI hG p.bound₀_nonneg hInv
      (hgrad t ht u hu huH hub hMA x hxs p.index) hβ0 (hβ1 p.index) hβ2
      (hF₁ t ht x hxs a) (hF₁ t ht x hxs p.index)
    exact hh.trans ((le_max_left C₀ C₁).trans (le_max_left _ _))
  · intro k
    have hh := scaled_tangentialFieldForcing_derivative_bound hu hF (hβs a)
      (fun i j => (smooth_variableInverseHessian hu hF i j).differentiable (by simp)) x a p.index k
      hr.le hr1 hI hCₐ hG hH p.bound₀_nonneg p.bound₁_nonneg hInv (hDB k)
      (hgrad t ht u hu huH hub hMA x hxs p.index)
      (hHess t ht u hu huH hub hMA x hxs p.index k) hβ0 (hβ1 k) hβ2
      (fun i j => hβ3 x hxp a i j k) (hF₁ t ht x hxs p.index)
      (hF₂ t ht x hxs a k) (hF₂ t ht x hxs p.index k)
    exact hh.trans ((le_max_right C₀ C₁).trans (le_max_left _ _))

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
