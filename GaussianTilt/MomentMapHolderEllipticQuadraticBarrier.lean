import GaussianTilt.MomentMapHolderEllipticBarrier

/-! # A constructed quadratic barrier for the actual linear inverse -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Matrix
open scoped Topology ContDiff
namespace GaussianTilt.HolderSpace
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- A single literal coordinate quadratic gives the uniform C⁰ inverse
bound. No defining-function or barrier-existence hypothesis is needed. -/
theorem ellipticDirichletOperator_value_norm_le_quadratic [NeZero n]
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α : ℝ} (hα : 0 < α) (A : Fin n → Fin n → Space S ℝ α)
    (hA : ∀ x ∈ interior S, (coefficientExtension α A x).PosDef)
    (i : Fin n) {lam R : ℝ} (hlam : 0 < lam) (hR : 0 ≤ R)
    (hdiag : ∀ x ∈ interior S, lam ≤ coefficientExtension α A x i i)
    (hstrip : ∀ x ∈ S, |x i| ≤ R)
    (j : zeroBoundary Coord ℝ hS α) :
    ‖value S ℝ α (jetValue Coord ℝ hS α j.1)‖ ≤
      (R ^ 2 / (2 * lam)) * ‖ellipticDirichletOperator hS α A j‖ := by
  let q : Coord (n := n) → ℝ := fun x => (x i) ^ 2 / 2
  let w : Coord (n := n) → ℝ := fun x => lam⁻¹ * (q x + (-(R^2/2)))
  have hq : ContDiff ℝ 2 q := by dsimp [q]; fun_prop
  have hw : ContDiff ℝ 2 w := contDiff_const.mul (hq.add contDiff_const)
  have hwlap (x : Coord) (hx : x ∈ interior S) :
      1 ≤ linearizedMA (coefficientExtension α A x) w x := by
    rw [linearizedMA_const_mul_at _ (hq.contDiffAt.add contDiffAt_const),
      linearizedMA_add_at _ hq.contDiffAt contDiffAt_const, linearizedMA_const,
      add_zero, linearizedMA_coordinate_half_sq]
    have hb := mul_le_mul_of_nonneg_left (hdiag x hx) (inv_nonneg.mpr hlam.le)
    simpa only [inv_mul_cancel₀ hlam.ne'] using hb
  have hsq (x : Coord) (hx : x ∈ S) : (x i)^2 ≤ R^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i)) hR).mpr (hstrip x hx)
  have hwneg (x : Coord) (hx : x ∈ S) : w x ≤ 0 := by
    dsimp [w, q]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hlam.le) (by nlinarith [hsq x hx])
  have hwbound (x : Coord) (hx : x ∈ S) : |w x| ≤ R^2/(2*lam) := by
    rw [abs_of_nonpos (hwneg x hx)]
    dsimp [w, q]
    have he : R^2/(2*lam) = lam⁻¹ * (R^2/2) := by field_simp
    rw [he]
    have hp := mul_nonneg (inv_nonneg.mpr hlam.le) (sq_nonneg (x i))
    nlinarith
  exact ellipticDirichletOperator_value_norm_le_barrier hS hSc hα A hA hw.continuous.continuousOn
    (fun _ _ => hw.contDiffAt) hwlap (fun x hx => hwneg x (hSc.isClosed.frontier_subset hx))
    (by positivity) hwbound j

end GaussianTilt.HolderSpace
