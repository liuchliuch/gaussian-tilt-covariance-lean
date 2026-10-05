import GaussianTilt.MomentMapClassicalDirichletIntrinsicForcing
import GaussianTilt.MomentMapClassicalDirichletTangentialForcingBounds
import GaussianTilt.MomentMapClassicalDirichletLocalExtension

/-! # Actual scale-uniform chart forcing bounds for intrinsic Hölder jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Fixed smooth chart representatives, and actual bounded/rescaled forcing
for intrinsic jets with interior smoothness only. -/
theorem intrinsic_dirichletContinuation_chart_forcing_bounds [NeZero n] {α : ℝ} (hα : 0 < α)
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ x ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 x] boundaryChartCoefficient d.coordinateDefining p.index a) ∧
      ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ x ∈ Metric.closedBall p.center p.radius, ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ < r →
        y ∈ interior {z | d.coordinateDefining z ≤ 0}) → ∀ a,
      let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
      |intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index x| ≤ C ∧
      ∀ k, r*|coordinateDerivative k (intrinsicTangentSource d.coordinate_body_convex α j.1 F (β a) a p.index) x| ≤ C := by
  obtain ⟨β,B₃,hB₃,hβs,heβ,hβ3⟩ := p.exists_smooth_chart_representatives_with_third_bound d.coordinateDefining_smooth
  obtain ⟨G,hG,hgrad⟩ := d.intrinsic_dirichletContinuation_uniform_first hα
  obtain ⟨H,hH,hHess⟩ := d.intrinsic_dirichletContinuation_uniform_hessian hα
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₁,hK₁,hF₁⟩ := dirichletContinuationDensity_uniform_log_coordinateDerivative d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K₂,hK₂,hF₂⟩ := dirichletContinuationDensity_uniform_log_hessian d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨Cₐ,hCₐ,hDA⟩ := d.intrinsic_dirichletContinuation_scaled_inverse_derivative_bound hα
  let I := ((n.factorial:ℝ)*(max H 1)^n)/c
  have hI : 0 ≤ I := by dsimp [I]; positivity
  let C₀ := K₁+p.bound₀*K₁+G*((n:ℝ)^2*I*p.bound₂)+2*p.bound₁
  let C₁ := K₂+p.bound₁*K₁+p.bound₀*K₂+H*((n:ℝ)^2*I*p.bound₂)+
    G*((n:ℝ)^2*(Cₐ*p.bound₂+I*B₃))+2*p.bound₂
  let C := max (max C₀ C₁) 0
  refine ⟨β,C,le_max_right _ _,hβs,heβ,?_⟩
  intro t ht j hs hp hMA x hxp r hr hr1 hball a
  let F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y)
  have hx : x ∈ interior {y | d.coordinateDefining y ≤ 0} := hball x (by simpa using hr)
  have hxs := interior_subset hx
  have hF : ContDiff ℝ ∞ F := by
    apply ContDiff.log _ (fun y => (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y)).ne')
    exact (contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp (contDiff_const.prodMk contDiff_id)
  have hMAlog (y : CoordinateSpace n) (hy : y ∈ interior {z | d.coordinateDefining z ≤ 0}) :
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y) := by
    dsimp [F]
    rw [Real.exp_log (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))]
    exact hMA y (interior_subset hy)
  obtain ⟨u,hu,hDu,hHu,hAux,hSource⟩ := intrinsic_local_representative_coefficient_source d.coordinate_body_convex
    hα j.1 hs (β := β a) hMAlog hx a p.index
  let B := variableInverseHessian u F
  have hInv : ∀ i l, |B x i l| ≤ I := by
    dsimp only [B]
    rw [← hAux.self_of_nhds]
    exact inverse_entry_bound_of_det_lower hc (by rw [hMA x hxs]; exact (hdens t ht x hxs).1)
      (hHess t ht j hs hp hMA x hxs)
  have hDB (k i l : Fin n) : r*|matrixCoordinateDerivative B k x i l| ≤ Cₐ := by
    have he : (fun y => B y i l) =ᶠ[𝓝 x] (fun y => (intrinsicHessian d.coordinate_body_convex α j.1 y)⁻¹ i l) :=
      hAux.symm.mono (fun y hy => congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i l) hy)
    change r*|coordinateDerivative k (fun y => B y i l) x| ≤ Cₐ
    rw [coordinateDerivative_congr_nhds he]
    exact hDA t ht j hs hp hMA x r hr hr1 hball k i l
  have hGrad (i : Fin n) : |coordinateDerivative i u x| ≤ G := by
    rw [← (hDu i).self_of_nhds]
    exact hgrad t ht j hs (fun y hy => hp y (interior_subset hy))
      (fun y hy => hMA y (interior_subset hy)) x hxs i
  have hHessU (i l : Fin n) : |coordinateHessian u x i l| ≤ H := by
    rw [← hHu.self_of_nhds]
    exact hHess t ht j hs hp hMA x hxs i l
  have hβ0 : |β a x| ≤ p.bound₀ := by rw [(heβ x hxp a).self_of_nhds]; exact p.value_bound x hxp a
  have hβ1 (k : Fin n) : |coordinateDerivative k (β a) x| ≤ p.bound₁ := by
    rw [coordinateDerivative_congr_nhds (heβ x hxp a)]
    exact p.derivative_bound x hxp a k
  have hβ2 (i l : Fin n) : |coordinateHessian (β a) x i l| ≤ p.bound₂ := by
    rw [coordinateHessian_congr_nhds (heβ x hxp a)]
    exact p.hessian_bound x hxp a i l
  constructor
  · rw [hSource.self_of_nhds]
    have hh := tangentialFieldForcing_abs_bound x a p.index hI hG p.bound₀_nonneg hInv
      (hGrad p.index) hβ0 (hβ1 p.index) hβ2 (hF₁ t ht x hxs a) (hF₁ t ht x hxs p.index)
    exact hh.trans ((le_max_left C₀ C₁).trans (le_max_left _ _))
  · intro k
    rw [coordinateDerivative_congr_nhds hSource]
    have hh := scaled_tangentialFieldForcing_derivative_bound hu hF (hβs a)
      (fun i l => (smooth_variableInverseHessian hu hF i l).differentiable (by simp)) x a p.index k
      hr.le hr1 hI hCₐ hG hH p.bound₀_nonneg p.bound₁_nonneg hInv (hDB k)
      (hGrad p.index) (hHessU p.index k) hβ0 (hβ1 k) hβ2
      (fun i l => hβ3 x hxp a i l k) (hF₁ t ht x hxs p.index)
      (hF₂ t ht x hxs a k) (hF₂ t ht x hxs p.index k)
    exact hh.trans ((le_max_right C₀ C₁).trans (le_max_left _ _))

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
