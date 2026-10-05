import GaussianTilt.MomentMapSchauderBoundaryHessianField

/-! # Actual closed half-ball geometry for the compatible boundary jet -/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma isCompact_flatClosedPatch (j : Fin n) (R : ℝ) : IsCompact (flatClosedPatch j R) :=
  (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous)

lemma convex_flatClosedPatch (j : Fin n) (R : ℝ) : Convex ℝ (flatClosedPatch j R) := by
  apply (convex_closedBall (0 : KernelSpace n) R).inter
  intro x hx y hy a b ha hb hab
  change 0 ≤ a*x j+b*y j
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

lemma flatClosedPatch_mem_interior {j : Fin n} {R : ℝ} {x : KernelSpace n}
    (hxn : ‖x‖ < R) (hxj : 0 < x j) : x ∈ interior (flatClosedPatch j R) := by
  let U : Set (KernelSpace n) := Metric.ball 0 R ∩ {x | 0 < x j}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous)
  have hUS : U ⊆ flatClosedPatch j R := fun y hy => ⟨Metric.ball_subset_closedBall hy.1, (show 0 < y j from hy.2).le⟩
  exact hU.subset_interior_iff.mpr hUS ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hxn, hxj⟩

lemma flatClosedPatch_nonempty_interior (j : Fin n) {R : ℝ} (hR : 0 < R) :
    (interior (flatClosedPatch j R)).Nonempty := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ j
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.basisFun_apply]
  refine ⟨(R/2) • e, flatClosedPatch_mem_interior ?_ ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hR), he, mul_one]
    linarith
  · simp only [PiLp.smul_apply, smul_eq_mul]
    have hej : e j = 1 := by simp [e, EuclideanSpace.basisFun_apply]
    rw [hej, mul_one]
    exact half_pos hR

lemma flatClosedPatch_interior_normal_pos {j : Fin n} {R : ℝ} {x : KernelSpace n}
    (hx : x ∈ interior (flatClosedPatch j R)) : 0 < x j := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let e := EuclideanSpace.basisFun (Fin n) ℝ j
  let y := x-(ε/2) • e
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.basisFun_apply]
  have hy : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hid : y-x = -((ε/2) • e) := by dsimp [y]; abel
    rw [hid, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε), he, mul_one]
    linarith
  have hyn : 0 ≤ y j := (hball hy).2
  have hej : e j = 1 := by simp [e, EuclideanSpace.basisFun_apply]
  change 0 ≤ x j-(ε/2)*e j at hyn
  rw [hej, mul_one] at hyn
  linarith

lemma flatClosedPatch_interior_subset_upper {j : Fin n} {R T : ℝ} (hRT : R < T) :
    interior (flatClosedPatch j R) ⊆ flatUpperBall j T := by
  intro x hx
  exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using (flat_patch_norm (interior_subset hx)).trans_lt hRT, flatClosedPatch_interior_normal_pos hx⟩

end GaussianTilt.MomentMapSchauder
