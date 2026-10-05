import GaussianTilt.MomentMapClassicalDirichletBarriers
import GaussianTilt.MomentMapClassicalDirichletCoordinateGradient
import GaussianTilt.MomentMapClassicalDirichletGeometryEllipticity

/-! # Parameter-uniform first-order estimates for the actual forcing homotopy -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Actual logarithmic spatial first derivatives have a parameter-uniform
bound, obtained from compact extrema and the positive density lower bound. -/
theorem dirichletContinuationDensity_uniform_log_coordinateDerivative
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (hH : ∀ x ∈ S, (coordinateHessian w x).PosDef) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ S, ∀ i,
      |coordinateDerivative i (fun y => Real.log (dirichletContinuationDensity w t y)) x| ≤ K := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := dirichletContinuationDensity_uniform_bounds hS hSn hw hH
  let g := fun x => (coordinateHessian w x).det
  have hg : ContDiff ℝ ∞ g := contDiff_matrix_det (smooth_coordinateHessian hw)
  have hgc : Continuous (coordinateGradient g) := continuous_pi (fun i =>
    (contDiff_coordinateDerivative hg (m := 0) (by simp) i).continuous)
  obtain ⟨J,hJ⟩ := hS.exists_bound_of_continuousOn hgc.continuousOn
  let B := max J 0
  have hB : 0 ≤ B := le_max_right _ _
  have hgb (x : CoordinateSpace n) (hx : x ∈ S) (i : Fin n) : |coordinateDerivative i g x| ≤ B :=
    (norm_le_pi_norm (coordinateGradient g x) i).trans ((hJ x hx).trans (le_max_left _ _))
  refine ⟨B/c, div_nonneg hB hc.le, ?_⟩
  intro t ht x hx i
  have hf : DifferentiableAt ℝ (dirichletContinuationDensity w t) x :=
    ((hg.differentiable (by simp) x).const_mul (1-t)).add (differentiableAt_const t)
  have hd : coordinateDerivative i (dirichletContinuationDensity w t) x =
      (1-t)*coordinateDerivative i g x := by
    unfold dirichletContinuationDensity
    rw [coordinateDerivative_add_at ((hg.differentiable (by simp) x).const_mul (1-t)) (differentiableAt_const t),
      coordinateDerivative_const_mul_at (hg.differentiable (by simp) x)]
    simp [coordinateDerivative]
  rw [coordinateDerivative_log_at hf (dirichletContinuationDensity_pos ht (hH x hx)).ne', hd,
    mul_comm (dirichletContinuationDensity w t x)⁻¹, ← div_eq_mul_inv, abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2),
    abs_of_pos (dirichletContinuationDensity_pos ht (hH x hx))]
  apply (div_le_div_of_nonneg_right
    (show (1-t)*|coordinateDerivative i g x| ≤ B from by
      calc
        _ ≤ 1*B := mul_le_mul (by linarith [ht.1]) (hgb x hx i) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _) (dirichletContinuationDensity_pos ht (hH x hx)).le).trans
  exact div_le_div_of_nonneg_left hB hc (hbounds t ht x hx).1

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The actual first derivatives of the fixed defining potential are
uniformly bounded on its compact coordinate body. -/
lemma coordinate_defining_first_bounds : ∃ W : ℝ, 0 ≤ W ∧
    (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, |d.coordinateDefining x| ≤ W) ∧
    (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, ∀ i, |coordinateDerivative i d.coordinateDefining x| ≤ W) := by
  have hc : Continuous (coordinateGradient d.coordinateDefining) := continuous_pi (fun i =>
    (contDiff_coordinateDerivative d.coordinateDefining_smooth (m := 0) (by simp) i).continuous)
  obtain ⟨U,hU⟩ := d.coordinate_body_compact.exists_bound_of_continuousOn d.coordinateDefining_smooth.continuous.continuousOn
  obtain ⟨V,hV⟩ := d.coordinate_body_compact.exists_bound_of_continuousOn hc.continuousOn
  let W := max (max U V) 0
  refine ⟨W, le_max_right _ _, ?_, ?_⟩
  · intro x hx
    exact (hU x hx).trans ((le_max_left U V).trans (le_max_left _ _))
  · intro x hx i
    exact (norm_le_pi_norm (coordinateGradient d.coordinateDefining x) i).trans
      ((hV x hx).trans ((le_max_right U V).trans (le_max_left _ _)))

/-- Uniform actual coordinate gradient control along the entire nonlinear
homotopy. Every constant is constructed from the fixed defining domain. -/
theorem dirichletContinuation_uniform_coordinate_gradient [NeZero n] :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ u : CoordinateSpace n → ℝ,
      ContDiff ℝ ∞ u →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0}, (coordinateHessian u x).PosDef) →
      (∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, u x = 0) →
      (∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (coordinateHessian u x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, ∀ i, |coordinateDerivative i u x| ≤ G := by
  obtain ⟨a,b,ha,hb,hbar⟩ := dirichletContinuation_scaled_barriers d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth
    (fun x _ => d.coordinateDefining_hessian_posDef x) d.coordinate_zero_boundary
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨K,hK,hKF⟩ := dirichletContinuationDensity_uniform_log_coordinateDerivative d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  obtain ⟨W,hW,hwW,hDw⟩ := d.coordinate_defining_first_bounds
  let B := K*max 1 D/d.modulus
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hK (zero_le_one.trans (le_max_left _ _))) d.modulus_pos.le
  refine ⟨b*W+B*W, add_nonneg (mul_nonneg hb.le hW) (mul_nonneg hB hW), ?_⟩
  intro t ht u hu hH hub hMA x hx i
  have hbar' := hbar t ht u hu.continuous.continuousOn
    (fun _ _ => (contDiff_infty.mp hu 2).contDiffAt) hH hub hMA
  have hzero : ∀ y, d.coordinateDefining y = 0 → u y = 0 := by
    intro y hy
    apply hub y
    rwa [d.coordinate_body_frontier]
  have hboundary : ∀ y ∈ frontier {y | d.coordinateDefining y ≤ 0}, ∀ i,
      |coordinateDerivative i u y| ≤ b*W := by
    intro y hy j
    exact boundary_coordinate_derivative_bound_of_barriers (hu.differentiable (by simp) y)
      (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt (d.coordinate_zero_boundary y hy)
      (d.coordinate_gradient_ne_zero (d.coordinate_zero_boundary y hy)) hzero ha.le hb.le
      hbar' (hDw y (d.coordinate_body_compact.isClosed.frontier_subset hy)) j
  have hpoint := coordinate_gradient_bound_from_boundary d.coordinateDefining_smooth hu
    d.coordinate_body_compact d.modulus_pos hK
    (fun y _ => d.coordinate_hessian_sub_modulus_posSemidef y) hH
    (F := fun y => Real.log (dirichletContinuationDensity d.coordinateDefining t y))
    (fun y hy => (hMA y hy).trans (Real.exp_log
      (dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef y))).symm)
    (fun y hy => hKF t ht y (interior_subset hy))
    (fun y hy => (hMA y hy).trans_le (hdens t ht y (interior_subset hy)).2) hboundary x hx i
  have hval := hwW x hx
  dsimp only [B] at *
  nlinarith [neg_abs_le (d.coordinateDefining x)]

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
