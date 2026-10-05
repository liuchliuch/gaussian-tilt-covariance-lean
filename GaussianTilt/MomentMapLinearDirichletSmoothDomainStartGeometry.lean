import GaussianTilt.MomentMapClassicalDirichletGeometryEllipticity
import GaussianTilt.MomentMapLinearDirichletHolderLaplace

/-! # Constructed strip and defining-barrier data for the genuine Laplace start -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Matrix
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Strong convexity of the fixed defining function supplies a strictly
positive Laplacian barrier; compactness supplies an actual bounded strip. -/
theorem exists_smoothDomain_laplace_start_geometry [NeZero n]
    {S A : Set (E n)} (d : SmoothInnerDomain S A) :
    ∃ (i : Fin n) (R a : ℝ), 0 ≤ R ∧ 0 < a ∧
      (∀ x, d.coordinateDefining x<0 → |x i| ≤ R) ∧
      (∀ x, a ≤ euclideanLaplacian d.coordinateDefining x) ∧
      (∀ x ∈ frontier {y | d.coordinateDefining y<0}, d.coordinateDefining x=0) := by
  let i : Fin n := ⟨0,NeZero.pos n⟩
  obtain ⟨B,hB⟩ := d.coordinate_body_compact.exists_bound_of_continuousOn
    (continuous_id : Continuous (fun x : CoordinateSpace n => x)).continuousOn
  refine ⟨i,max B 0,d.modulus*(n:ℝ),le_max_right _ _,mul_pos d.modulus_pos (by exact_mod_cast NeZero.pos n),?_,?_,?_⟩
  · intro x hx
    have hn : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact hn.trans ((hB x hx.le).trans (le_max_left _ _))
  · intro x
    have hh := d.modulus_mul_trace_le_hessian_trace x (B := (1 : Matrix (Fin n) (Fin n) ℝ)) Matrix.PosSemidef.one
    rw [Matrix.trace_one,Fintype.card_fin,Matrix.one_mul] at hh
    simpa only [Matrix.trace,Matrix.diag_apply,coordinateHessian,euclideanLaplacian] using hh
  · exact fun x hx => frontier_lt_subset_eq d.coordinateDefining_smooth.continuous continuous_const hx

end GaussianTilt.MomentMapLinearDirichlet
