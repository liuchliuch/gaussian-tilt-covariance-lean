import GaussianTilt.MomentMapSchauderBoundaryConvergence

/-! # Quantitative gluing of interior fields to their boundary limits -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1500000
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A direct near/far decomposition glues genuine interior Hölder control
and convergence to a Hölder boundary field. -/
theorem flat_field_holder_of_boundary_and_interior
    (j : Fin n) {S : Set (KernelSpace n)} (hS : ∀ x ∈ S, 0 ≤ x j)
    (G B : KernelSpace n → F) {α A J L : ℝ} (hα : 0 ≤ α)
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hL : 0 ≤ L)
    (herror : ∀ x ∈ S, ‖G x-B x‖ ≤ A*(x j)^α)
    (hboundary : ∀ x ∈ S, ∀ y ∈ S, ‖B x-B y‖ ≤ J*‖x-y‖^α)
    (hinterior : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ < x j/128 → ‖G x-G y‖ ≤ L*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖G x-G y‖ ≤ (L+A*(128^α+129^α)+J)*‖x-y‖^α := by
  intro x hx y hy
  by_cases hnear : ‖x-y‖ < x j/128
  · apply (hinterior x hx y hy hnear).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
    have hn : 0 ≤ A*(128^α+129^α) := by positivity
    linarith
  · have hxj : x j ≤ 128*‖x-y‖ := by linarith [le_of_not_gt hnear]
    have hyj : y j ≤ 129*‖x-y‖ := by
      have hh : |x j-y j| ≤ ‖x-y‖ := PiLp.norm_apply_le (x-y) j
      linarith [neg_abs_le (x j-y j)]
    have hxp : (x j)^α ≤ 128^α*‖x-y‖^α := by
      have hh := Real.rpow_le_rpow (hS x hx) hxj hα
      rwa [Real.mul_rpow (by norm_num : (0:ℝ)≤128) (norm_nonneg _)] at hh
    have hyp : (y j)^α ≤ 129^α*‖x-y‖^α := by
      have hh := Real.rpow_le_rpow (hS y hy) hyj hα
      rwa [Real.mul_rpow (by norm_num : (0:ℝ)≤129) (norm_nonneg _)] at hh
    have hxe := (herror x hx).trans (mul_le_mul_of_nonneg_left hxp hA)
    have hye := (herror y hy).trans (mul_le_mul_of_nonneg_left hyp hA)
    have hb := hboundary x hx y hy
    have ht : ‖G x-G y‖ ≤ ‖G x-B x‖+‖B x-B y‖+‖G y-B y‖ := by
      have h1 := norm_sub_le_norm_sub_add_norm_sub (G x) (B x) (G y)
      have h2 := norm_sub_le_norm_sub_add_norm_sub (B x) (B y) (G y)
      rw [norm_sub_rev (B y) (G y)] at h2
      linarith
    nlinarith [mul_nonneg hL (Real.rpow_nonneg (norm_nonneg (x-y)) α)]

/-- A literal Hölder bound proves continuity of a Banach-valued field on
its closed domain, including the interface where it was pieced together. -/
theorem continuousOn_of_norm_holder_bound {S : Set (KernelSpace n)} {G : KernelSpace n → F}
    {α C : ℝ} (hα : 0 < α)
    (hG : ∀ x ∈ S, ∀ y ∈ S, ‖G x-G y‖ ≤ C*‖x-y‖^α) : ContinuousOn G S := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun y : S => C*‖(y : KernelSpace n)-x‖^α) (𝓝 x) (𝓝 0) := by
    convert (continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      ((continuous_subtype_val.sub continuous_const).norm))).tendsto x using 1
    simp [Real.zero_rpow hα.ne']
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => hG y y.2 x x.2) ht

def flatProjection (j : Fin n) (x : KernelSpace n) : KernelSpace n :=
  x-x j • EuclideanSpace.basisFun (Fin n) ℝ j

lemma flatProjection_plane (j : Fin n) (x : KernelSpace n) : flatProjection j x j=0 := by
  simp [flatProjection]

lemma flatProjection_eq_self {j : Fin n} {x : KernelSpace n} (hx : x j=0) : flatProjection j x=x := by
  simp [flatProjection,hx]

lemma norm_sub_flatProjection_eq (j : Fin n) (x : KernelSpace n) : ‖x-flatProjection j x‖=|x j| := by
  simp only [flatProjection,sub_sub_cancel,norm_smul,Real.norm_eq_abs,
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one]

lemma flatProjection_lipschitz (j : Fin n) (x y : KernelSpace n) :
    ‖flatProjection j x-flatProjection j y‖ ≤ 2*‖x-y‖ := by
  have he : flatProjection j x-flatProjection j y=(x-y)-(x j-y j) • EuclideanSpace.basisFun (Fin n) ℝ j := by
    dsimp [flatProjection]
    module
  rw [he]
  have ht := norm_sub_le (x-y) ((x j-y j) • EuclideanSpace.basisFun (Fin n) ℝ j)
  rw [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] at ht
  have hh : |x j-y j| ≤ ‖x-y‖ := PiLp.norm_apply_le (x-y) j
  linarith

lemma norm_flatProjection_le (j : Fin n) (x : KernelSpace n) : ‖flatProjection j x‖ ≤ 2*‖x‖ := by
  simpa only [flatProjection,PiLp.zero_apply,zero_smul,sub_zero] using flatProjection_lipschitz j x 0

end GaussianTilt.MomentMapSchauder
