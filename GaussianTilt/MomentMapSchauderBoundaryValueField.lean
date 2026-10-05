import GaussianTilt.MomentMapSchauderBoundaryFirstField
import GaussianTilt.MomentMapHolderInteriorEmbedding

/-! # Actual derivative identities and value continuity up to the plane -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1400000
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma continuousOn_flat_patch_of_growth (j : Fin n) {u : KernelSpace n → ℝ} {R A : ℝ}
    (hR : R < 2) (hu : ContinuousOn u (flatUpperBall j 2))
    (hzero : ∀ x, x j ≤ 0 → u x=0)
    (hbound : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ A*|x j|) :
    ContinuousOn u (flatClosedPatch j R) := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hxB : (x : KernelSpace n) ∈ Metric.ball (0 : KernelSpace n) 2 := by
    rw [Metric.mem_ball,dist_zero_right]
    exact (flat_patch_norm x.2).trans_lt hR
  by_cases hxj : 0 < (x : KernelSpace n) j
  · exact (hu.continuousAt ((isOpen_flatUpperBall j 2).mem_nhds ⟨hxB,hxj⟩)).comp
      continuous_subtype_val.continuousAt
  · have hx0 : (x : KernelSpace n) j=0 := le_antisymm (le_of_not_gt hxj) x.2.2
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have ht : Tendsto (fun y : flatClosedPatch j R => A*|(y : KernelSpace n) j|) (𝓝 x) (𝓝 0) := by
      convert (continuous_const.mul (((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous.comp
        continuous_subtype_val).abs)).tendsto x using 1
      simp [hx0]
    apply squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) ht
    change ‖u y-u x‖ ≤ A*|(y : KernelSpace n) j|
    rw [hzero x hx0.le,sub_zero,Real.norm_eq_abs]
    exact hbound y (by
      rw [Metric.mem_ball,dist_zero_right]
      exact (flat_patch_norm y.2).trans_lt hR)

lemma flatFirstField_eventuallyEq_fderiv (j : Fin n) (u : KernelSpace n → ℝ)
    (p : KernelSpace n → KernelSpace n) {x : KernelSpace n} (hx : 0 < x j) :
    flatFirstField j u p =ᶠ[𝓝 x] fderiv ℝ u := by
  have hn : {y : KernelSpace n | 0 < y j} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous).mem_nhds hx
  filter_upwards [hn] with y hy
  simp only [flatFirstField,if_pos hy]

lemma hasFDerivAt_flat_value (j : Fin n) {u : KernelSpace n → ℝ}
    (p : KernelSpace n → KernelSpace n) {x : KernelSpace n}
    (hu : ContDiffAt ℝ 2 u x) (hx : 0 < x j) :
    HasFDerivAt u (flatFirstField j u p x) x := by
  rw [flatFirstField,if_pos hx]
  exact (hu.differentiableAt (by norm_num)).hasFDerivAt

lemma hasFDerivAt_flatFirstField (j : Fin n) {u : KernelSpace n → ℝ}
    (p : KernelSpace n → KernelSpace n) (T : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n)
    {x : KernelSpace n} (hu : ContDiffAt ℝ 2 u x) (hx : 0 < x j) :
    HasFDerivAt (flatFirstField j u p) (flatSecondField j u T x) x := by
  rw [flatSecondField,if_pos hx]
  exact ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl).hasFDerivAt.congr_of_eventuallyEq
    (flatFirstField_eventuallyEq_fderiv j u p hx)

end GaussianTilt.MomentMapSchauder
