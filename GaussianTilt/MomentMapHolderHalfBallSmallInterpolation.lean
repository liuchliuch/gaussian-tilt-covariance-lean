import GaussianTilt.MomentMapHolderHalfBallInterpolation

/-! # Tunably small highest-order contribution in genuine one-sided interpolation -/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.HolderSpace
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- The interpolation radius is constructed before the unknown jet. -/
theorem halfBall_jet_derivatives_small_highest_norm
    (q : Fin n) {R α ε : ℝ} (hR : 0 < R) (hα : 0 < α) (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (J : Jet (KernelSpace n) ℝ (convex_flatClosedPatch q R) α)
      (U : ℝ), 0 ≤ U →
      (∀ y : flatClosedPatch q R,
        |value (flatClosedPatch q R) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) y| ≤ U) →
      ∀ x : flatClosedPatch q R, ‖(x : KernelSpace n)‖ ≤ R/2 →
      ‖value (flatClosedPatch q R) (KernelSpace n →L[ℝ] ℝ) α
        (jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) x‖ ≤
        L*U + ε*‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J‖ ∧
      ‖value (flatClosedPatch q R) (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α
        (jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J) x‖ ≤
        L*U + ε*‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J‖ := by
  have hc : ContinuousAt (fun r : ℝ => (64 : ℝ)*r^α) 0 :=
    continuous_const.continuousAt.mul (Real.continuous_rpow_const hα.le).continuousAt
  have he : ∀ᶠ r : ℝ in 𝓝 0, (64 : ℝ)*r^α < ε :=
    hc.eventually (eventually_lt_nhds (by simpa [Real.zero_rpow hα.ne'] using hε))
  have hrsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r ≤ R/2 ∧ r ≤ 1 ∧ (64 : ℝ)*r^α ≤ ε := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds he,
      nhdsWithin_le_nhds (eventually_lt_nhds (half_pos hR)),
      nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ)<1 by norm_num))] with r hr he hrR hr1
    exact ⟨hr, hrR.le, hr1.le, he.le⟩
  obtain ⟨r, hr, hrR, hr1, h64⟩ := hrsmall.exists
  let L := max (36/r) (64/r^2)
  have hL : 0 ≤ L := (by positivity : 0 ≤ (36 : ℝ)/r).trans (le_max_left _ _)
  refine ⟨L, hL, ?_⟩
  intro J U hU hu x hx
  have hh := halfBall_jet_derivative_interpolation q hR hα hU J hu hr hrR x hx
  let T := ‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q R) α J‖
  have hT : 0 ≤ T := norm_nonneg _
  have hrp : 0 ≤ r^α := Real.rpow_nonneg hr.le _
  have h36 : 36*r^α*r ≤ ε := by
    have h1 := mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ (36 : ℝ)*r^α)
    nlinarith
  constructor
  · apply hh.1.trans
    have hleft : 36*U/r ≤ L*U := by
      convert mul_le_mul_of_nonneg_right (le_max_left (36/r) (64/r^2)) hU using 1 <;> ring
    have hright : 36*T*r^α*r ≤ ε*T := by
      convert mul_le_mul_of_nonneg_right h36 hT using 1 <;> ring
    exact add_le_add hleft hright
  · apply hh.2.trans
    have hleft : 64*U/r^2 ≤ L*U := by
      convert mul_le_mul_of_nonneg_right (le_max_right (36/r) (64/r^2)) hU using 1 <;> ring
    have hright : 64*T*r^α ≤ ε*T := by
      convert mul_le_mul_of_nonneg_right h64 hT using 1 <;> ring
    exact add_le_add hleft hright

end GaussianTilt.HolderSpace
