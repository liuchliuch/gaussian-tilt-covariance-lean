import GaussianTilt.MomentMapClassicalDirichletIntrinsicHessian
import GaussianTilt.MomentMapClassicalDirichletUniformEllipticity

/-! # Derived uniform ellipticity for genuine intrinsic Dirichlet jets -/
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

/-- Uniform inverse ellipticity is derived for the actual intrinsic second
field, requiring smoothness only in the source interior. -/
theorem intrinsic_dirichletContinuation_uniform_inverse_ellipticity [NeZero n] {α : ℝ} (hα : 0 < α) :
    ∃ lam Λ : ℝ, 0 < lam ∧ 0 < Λ ∧ ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).PosDef) →
      (∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 x).det = dirichletContinuationDensity d.coordinateDefining t x) →
      ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, ∀ v : CoordinateSpace n,
        lam*(v ⬝ᵥ v) ≤ v ⬝ᵥ ((intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ *ᵥ v) ∧
        v ⬝ᵥ ((intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ *ᵥ v) ≤ Λ*(v ⬝ᵥ v) := by
  obtain ⟨K,hK,hKH⟩ := d.intrinsic_dirichletContinuation_uniform_hessian hα
  obtain ⟨c,D,hc,hD,hdens⟩ := dirichletContinuationDensity_uniform_bounds d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth (fun x _ => d.coordinateDefining_hessian_posDef x)
  let U := (n:ℝ)^2*max K 1
  let I := ((n.factorial:ℝ)*(max K 1)^n)/c
  let Λ := (n:ℝ)^2*max I 1
  have hn : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hU : 0 < U := mul_pos (sq_pos_of_pos hn) (zero_lt_one.trans_le (le_max_right _ _))
  have hΛ : 0 < Λ := mul_pos (sq_pos_of_pos hn) (zero_lt_one.trans_le (le_max_right _ _))
  refine ⟨U⁻¹,Λ,inv_pos.mpr hU,hΛ,?_⟩
  intro t ht j hs hp hMA x hx v
  have hentry := hKH t ht j hs hp hMA x hx
  have hdet : c ≤ (intrinsicHessian d.coordinate_body_convex α j.1 x).det := by
    rw [hMA x hx]
    exact (hdens t ht x hx).1
  have hupper (z : CoordinateSpace n) :
      z ⬝ᵥ (intrinsicHessian d.coordinate_body_convex α j.1 x *ᵥ z) ≤ U*(z ⬝ᵥ z) := by
    have hh := quadraticForm_upper_of_entry_bound (zero_le_one.trans (le_max_right K 1))
      (fun i l => (hentry i l).trans (le_max_left K 1)) z
    rwa [coordinateEuclidean_norm_sq] at hh
  refine ⟨inverse_quadratic_lower_of_quadratic_upper (hp x hx) hU hupper v,?_⟩
  have hInv (i l : Fin n) : |(intrinsicHessian d.coordinate_body_convex α j.1 x)⁻¹ i l| ≤ max I 1 :=
    (inverse_entry_bound_of_det_lower hc hdet hentry i l).trans (le_max_left _ _)
  have hh := quadraticForm_upper_of_entry_bound (zero_le_one.trans (le_max_right I 1)) hInv v
  rwa [coordinateEuclidean_norm_sq] at hh

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
