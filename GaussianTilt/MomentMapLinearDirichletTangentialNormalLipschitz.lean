import GaussianTilt.MomentMapLinearDirichletTangentialNormalClosed
import GaussianTilt.MomentMapClassicalDirichletIntrinsicLipschitz

/-! # The proved first C² pass gives an actual Lipschitz first gradient

This is the noncircular input for the full-exponent second boundary pass.
The finite Hessian bound is constructed from the continuous recovered
field on the compact closed patch, rather than assumed for a weak solution.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- An actual continuous closed-body derivative field has a constructed
finite bound, and convex mean value turns it into a true Lipschitz bound. -/
theorem exists_lipschitz_gradient_of_closed_coordinate_fields
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S)
    {G : CoordinateSpace n → CoordinateSpace n}
    {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ k i,ContinuousOn (fun x=>H x k i) S)
    (hd : ∀ k x,x∈S → HasFDerivWithinAt (fun y=>G y k) (coordinateCovector (H x k)) S x) :
    ∃ C : ℝ,0≤C ∧ ∀ k x,x∈S → ∀ y,y∈S → |G x k-G y k|≤C*‖x-y‖ := by
  have hHc : ContinuousOn H S := continuousOn_pi.mpr (fun k=>continuousOn_pi.mpr (hH k))
  obtain ⟨M,hM⟩ := hSc.exists_bound_of_continuousOn hHc
  let B := max M 0
  have hB : 0≤B := le_max_right _ _
  have hb (x : CoordinateSpace n) (hx : x∈S) (k i : Fin n) : |H x k i|≤B :=
    ((norm_le_pi_norm (H x k) i).trans (norm_le_pi_norm (H x) k)).trans ((hM x hx).trans (le_max_left _ _))
  refine ⟨(n:ℝ)*B,mul_nonneg (Nat.cast_nonneg _) hB,?_⟩
  intro k x hx y hy
  have hnorm (z : CoordinateSpace n) (hz : z∈S) : ‖coordinateCovector (H z k)‖≤(n:ℝ)*B :=
    norm_covector_le_of_coordinate_bound _ hB (by simpa only [coordinateCovector_single] using hb z hz k)
  simpa only [Real.norm_eq_abs] using hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz=>hd k z hz) hnorm hy hx

end GaussianTilt.MomentMapLinearDirichlet
