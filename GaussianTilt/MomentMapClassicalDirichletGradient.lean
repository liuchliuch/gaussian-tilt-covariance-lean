import GaussianTilt.MomentMapClassicalDirichletBarriers
import GaussianTilt.MomentMapRegularityConstantDensityGeometry
import GaussianTilt.MomentMapRegularitySecondOrderInterpolation

/-!
# Boundary-barrier control of actual gradients

A lower defining-function barrier and convexity control every interior
supporting slope uniformly, including as the source point approaches the
boundary. This supplies a first-order a priori estimate from actual
Dirichlet barriers, not from an assumed Hessian bound.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- A convex zero-boundary potential trapped above a Lipschitz lower
barrier has uniformly bounded true supporting slopes throughout the domain. -/
theorem supporting_slope_bound_of_dirichlet_barrier [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) {u w : E n → ℝ}
    {L : ℝ≥0} (hwL : LipschitzOnWith L w S)
    (hwb : ∀ y ∈ frontier S, w y = 0)
    {b : ℝ} (hb : 0 ≤ b) (hlo : ∀ y ∈ S, b * w y ≤ u y)
    (hup : ∀ y ∈ S, u y ≤ 0) {x p : E n} (hx : x ∈ interior S)
    (hp : SupportsOn S u p x) : ‖p‖ ≤ b * L := by
  have hxS := interior_subset hx
  obtain ⟨y, hy, hxy⟩ := hS.exists_mem_frontier_infDist_compl_eq_dist hxS
  let d : ℝ := Metric.infDist x Sᶜ
  have hd : 0 < d := by
    apply (Metric.infDist_pos_iff_notMem_closure (nonempty_compl.mpr hS.ne_univ)).mp
    rw [closure_compl]
    exact fun h => h hx
  have hball : Metric.closedBall x d ⊆ S := by
    have h := Metric.closedBall_infDist_compl_subset_closure hxS
    simpa only [hS.isClosed.closure_eq] using h
  have hnorm : ‖p‖ ≤ (-u x) / d := by
    have h := supporting_slope_error_of_upper_approximation (q := 0) hd
      (neg_nonneg.mpr (hup x hxS)) (fun z hz => hp z (hball hz))
      (fun z hz => by simpa only [inner_zero_left, sub_zero, zero_sub] using
        sub_le_sub_right (hup z (hball hz)) (u x))
    simpa only [sub_zero] using h
  have hwy := hwL.dist_le_mul x hxS y (hS.isClosed.frontier_subset hy)
  rw [hwb y hy, Real.dist_eq, sub_zero, ← hxy] at hwy
  have hlower := hlo x hxS
  have hnum : -u x ≤ b * (L : ℝ) * d := by
    have hmul := mul_le_mul_of_nonneg_left hwy hb
    dsimp [d] at *
    nlinarith [neg_abs_le (w x)]
  apply hnorm.trans
  exact (div_le_iff₀ hd).mpr hnum

/-- The actual gradient obeys the boundary-barrier slope estimate. -/
theorem gradient_bound_of_dirichlet_barrier [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) {u w : E n → ℝ}
    (hu : ConvexOn ℝ S u) {L : ℝ≥0} (hwL : LipschitzOnWith L w S)
    (hwb : ∀ y ∈ frontier S, w y = 0)
    {b : ℝ} (hb : 0 ≤ b) (hlo : ∀ y ∈ S, b * w y ≤ u y)
    (hup : ∀ y ∈ S, u y ≤ 0) {x : E n} (hx : x ∈ interior S)
    (hud : DifferentiableAt ℝ u x) : ‖gradient u x‖ ≤ b * L := by
  exact supporting_slope_bound_of_dirichlet_barrier hS hwL hwb hb hlo hup hx
    (supportsOn_gradient_of_convexOn hu (interior_subset hx) hud)

/-- The Lipschitz constant of a smooth defining function on a compact
convex domain is constructed from the maximum of its actual first derivative. -/
theorem exists_lipschitzOnWith_of_smooth_on_compact_convex
    {S : Set (E n)} (hS : IsCompact S) (hSc : Convex ℝ S)
    {w : E n → ℝ} (hw : ContDiff ℝ 1 w) : ∃ L : ℝ≥0, LipschitzOnWith L w S := by
  have hdc : Continuous (fderiv ℝ w) := hw.continuous_fderiv le_rfl
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hdc.continuousOn
  let L : ℝ≥0 := (max B 0).toNNReal
  refine ⟨L, hSc.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hw.differentiable le_rfl x) ?_⟩
  intro x hx
  have hb := (hB x hx).trans (le_max_left B 0)
  change ‖fderiv ℝ w x‖ ≤ (L : ℝ)
  simpa only [L, Real.coe_toNNReal (max B 0) (le_max_right B 0)] using hb

end GaussianTilt.MomentMapRegularity
