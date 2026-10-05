import GaussianTilt.MomentMapLinearDirichletVariableWeakFlattening
import GaussianTilt.MomentMapSchauderGlobalChartRecovery

/-! # A globally smooth genuine inverse boundary chart in Euclidean coordinates -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def scaledFlatteningMap (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n) (s : ℝ) (x : KernelSpace n) : KernelSpace n :=
  s⁻¹ • flatteningMap w a j x

lemma contDiff_scaledFlatteningMap {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n) (s : ℝ) : ContDiff ℝ ∞ (scaledFlatteningMap w a j s) :=
  contDiff_const.smul (contDiff_flatteningMap hw a j)

lemma scaledFlatteningMap_normal (w : KernelSpace n → ℝ) (a x : KernelSpace n) (j : Fin n) (s : ℝ) :
    scaledFlatteningMap w a j s x j= -(s⁻¹*(w x-w a)) := by
  simp only [scaledFlatteningMap,PiLp.smul_apply,smul_eq_mul,flatteningMap_normal,mul_neg]

lemma scaledFlatteningMap_self (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n) (s : ℝ) :
    scaledFlatteningMap w a j s a=0 := by simp only [scaledFlatteningMap,flatteningMap_self,smul_zero]

/-- The inverse model is genuinely globally smooth and agrees as an
actual neighborhood germ with the true scaled local inverse at every
point of the closed unit ball. Both inverse identities and the exact
level relation are proved, rather than supplied as chart premises. -/
theorem exists_global_euclidean_boundary_chart {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0) :
    ∃ s : ℝ, ∃ ψ : KernelSpace n → KernelSpace n, 0 < s ∧ s ≤ 1 ∧ ContDiff ℝ ∞ ψ ∧ ψ 0=a ∧
      (∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1,
        ψ =ᶠ[𝓝 z] (fun y => (regularLevelFlatteningChart hw a j hj).symm (s • y))) ∧
      (∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, w (ψ z)=w a-s*z j) ∧
      (∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, scaledFlatteningMap w a j s (ψ z)=z) ∧
      (∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, ψ z ∈ (regularLevelFlatteningChart hw a j hj).source) ∧
      (∀ x ∈ (regularLevelFlatteningChart hw a j hj).source,
        ‖scaledFlatteningMap w a j s x‖ ≤ 1 → ψ (scaledFlatteningMap w a j s x)=x) := by
  obtain ⟨q,hq,hInv⟩ := exists_regularLevelFlattening_inverse_ball hw a j hj
  let s := min 1 (q/4)
  have hs : 0 < s := lt_min zero_lt_one (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have h2s : 2*s < q := by have hh := min_le_right (1:ℝ) (q/4); dsimp [s]; linarith
  have hi : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) (2*s),
      z ∈ (regularLevelFlatteningChart hw a j hj).target ∧ ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z := by
    intro z hz
    have hh := hInv z (Metric.closedBall_subset_ball h2s hz)
    exact ⟨hh.1,hh.2.1⟩
  obtain ⟨ψ0,C,hψ0,hC,he0,_,hw0⟩ := exists_actual_flattening_pullback_model hw a j hj hs hi
  let c := coordinateEquiv n
  let ψ := fun z : KernelSpace n => c.symm (ψ0 (c z))
  have hψ : ContDiff ℝ ∞ ψ := c.symm.contDiff.comp (hψ0.comp c.contDiff)
  have hraw (z : KernelSpace n) (hz : z ∈ Metric.closedBall (0 : KernelSpace n) 1) : c z ∈ rawChartClosedBall (n := n) 1 := by
    change ‖c.symm (c z)‖ ≤ 1
    rw [c.symm_apply_apply]
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  have he : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1,
      ψ =ᶠ[𝓝 z] (fun y => (regularLevelFlatteningChart hw a j hj).symm (s • y)) := by
    intro z hz
    have hh := (he0 (c z) (hraw z hz)).comp_tendsto (c.continuous.tendsto z)
    filter_upwards [hh] with y hy
    change c.symm (ψ0 (c y))=_
    dsimp only [Function.comp_apply] at hy
    rw [hy]
    simp only [scaledRawInverseChart,c,ContinuousLinearEquiv.symm_apply_apply]
  have hzero : ψ 0=a := by
    have hh := (he 0 (Metric.mem_closedBall_self zero_le_one)).self_of_nhds
    simpa only [smul_zero,regularLevelFlatteningChart_symm_zero] using hh
  have hlevel : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, w (ψ z)=w a-s*z j := by
    intro z hz
    exact hw0 (c z) (hraw z hz)
  have hsz (z : KernelSpace n) (hz : z ∈ Metric.closedBall (0 : KernelSpace n) 1) :
      s • z ∈ Metric.closedBall (0 : KernelSpace n) (2*s) := by
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    have hn : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    nlinarith
  refine ⟨s,ψ,hs,hs1,hψ,hzero,he,hlevel,?_,?_,?_⟩
  · intro z hz
    rw [scaledFlatteningMap,(he z hz).self_of_nhds]
    have hh := (regularLevelFlatteningChart hw a j hj).right_inv (hi _ (hsz z hz)).1
    change flatteningMap w a j ((regularLevelFlatteningChart hw a j hj).symm (s • z))=s • z at hh
    rw [hh,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
  · intro z hz
    rw [(he z hz).self_of_nhds]
    exact (regularLevelFlatteningChart hw a j hj).map_target (hi _ (hsz z hz)).1
  · intro x hx hn
    have hz : scaledFlatteningMap w a j s x ∈ Metric.closedBall (0 : KernelSpace n) 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hn
    rw [(he _ hz).self_of_nhds]
    dsimp only [scaledFlatteningMap]
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    exact (regularLevelFlatteningChart hw a j hj).left_inv hx

end GaussianTilt.MomentMapSchauder
