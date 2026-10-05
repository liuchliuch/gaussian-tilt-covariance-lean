import GaussianTilt.MomentMapSchauderBoundaryVariableAffineBounds
import GaussianTilt.MomentMapSchauderBoundedHolder

/-! # True closure jets under the constructed boundary-preserving affine map -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma secondFrechet_comp_equiv_at (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    {u : KernelSpace n → ℝ} {x : KernelSpace n} (hu : ContDiffAt ℝ 2 u (P x)) :
    fderiv ℝ (fderiv ℝ (u ∘ P)) x=(fderiv ℝ (fderiv ℝ u) (P x)).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap := by
  obtain ⟨v,hv,he⟩ := exists_global_contDiff_eventuallyEq 2 hu
  have heP : v ∘ P =ᶠ[𝓝 x] u ∘ P := he.comp_tendsto (P.continuous.tendsto x)
  rw [← heP.fderiv.fderiv_eq]
  change fderiv ℝ (fderiv ℝ (v ∘ P.toContinuousLinearMap)) x=_
  rw [secondFrechet_comp_linear hv P.toContinuousLinearMap]
  change (fderiv ℝ (fderiv ℝ v) (P x)).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap=_
  rw [he.fderiv.fderiv_eq]

lemma norm_comp_linear_le {D : KernelSpace n →L[ℝ] ℝ}
    (P : KernelSpace n ≃L[ℝ] KernelSpace n) {M V : ℝ} (hP : ‖P.toContinuousLinearMap‖ ≤ M)
    (hD : ‖D‖ ≤ V) (hV : 0 ≤ V) : ‖D.comp P.toContinuousLinearMap‖ ≤ M*V := by
  exact D.opNorm_comp_le P.toContinuousLinearMap |>.trans
    ((mul_le_mul hD hP (norm_nonneg _) hV).trans_eq (mul_comm V M))

lemma boundaryPullbackFirst_holder (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ) {S T : Set (KernelSpace n)} (hmap : MapsTo P S T)
    {α H M : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hP : ‖P.toContinuousLinearMap‖ ≤ M)
    (hD : ∀ x ∈ T, ∀ y ∈ T, ‖D x-D y‖ ≤ H*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖(D (P x)).comp P.toContinuousLinearMap-(D (P y)).comp P.toContinuousLinearMap‖ ≤
      (M*H*M^α)*‖x-y‖^α := by
  intro x hx y hy
  have he : (D (P x)).comp P.toContinuousLinearMap-(D (P y)).comp P.toContinuousLinearMap=
      (D (P x)-D (P y)).comp P.toContinuousLinearMap := by ext v; simp
  rw [he]
  have hn : ‖P x-P y‖ ≤ M*‖x-y‖ := by
    rw [← map_sub]
    exact (P.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  have hh := (hD _ (hmap hx) _ (hmap hy)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hn hα) hH)
  rw [Real.mul_rpow hM (norm_nonneg _)] at hh
  exact (norm_comp_linear_le P hP hh (by positivity)).trans_eq (by ring)

lemma boundedHolderOn_boundaryPullbackHessian (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    {B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ}
    {S T : Set (KernelSpace n)} (hmap : MapsTo P S T) {α : ℝ} (hα : 0 ≤ α)
    (hB : BoundedHolderOn α B T) :
    BoundedHolderOn α (fun x => (B (P x)).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap) S := by
  obtain ⟨Q,hQ,hQb,hQH⟩ := hB
  let M := ‖P.toContinuousLinearMap‖
  have hM : 0 ≤ M := norm_nonneg _
  refine ⟨M^2*Q*(1+M^α),by positivity,?_,?_⟩
  · intro x hx
    have hh := (norm_bilinearComp_same_le (B (P x)) P.toContinuousLinearMap).trans
      (mul_le_mul_of_nonneg_right (hQb _ (hmap hx)) (sq_nonneg M))
    apply hh.trans
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg M) hQ) (Real.rpow_nonneg hM α)]
  · intro x hx y hy
    have hh := boundaryPullbackHessian_holder P B hmap hα hQ hM le_rfl hQH x hx y hy
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
    nlinarith

lemma scalar_holder_comp_equiv (P : KernelSpace n ≃L[ℝ] KernelSpace n) {f : KernelSpace n → ℝ}
    {S T : Set (KernelSpace n)} (hmap : MapsTo P S T) {α H M : ℝ}
    (hα : 0 ≤ α) (hH : 0 ≤ H) (hM : 0 ≤ M) (hP : ‖P.toContinuousLinearMap‖ ≤ M)
    (hf : ∀ x ∈ T, ∀ y ∈ T, |f x-f y| ≤ H*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S, |f (P x)-f (P y)| ≤ (H*M^α)*‖x-y‖^α := by
  intro x hx y hy
  have hn : ‖P x-P y‖ ≤ M*‖x-y‖ := by
    rw [← map_sub]
    exact (P.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  have hh := (hf _ (hmap hx) _ (hmap hy)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hn hα) hH)
  rw [Real.mul_rpow hM (norm_nonneg _)] at hh
  exact hh.trans_eq (by ring)

end GaussianTilt.MomentMapSchauder
