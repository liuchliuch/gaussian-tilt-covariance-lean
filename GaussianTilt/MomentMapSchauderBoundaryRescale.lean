import GaussianTilt.MomentMapSchauderBoundaryLocalPoisson
import GaussianTilt.MomentMapLinearDirichletFlatTaylorJets

/-! # Local affine scaling for the true interior derivative fields -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma secondFrechet_comp_add_right (u : KernelSpace n → ℝ) (a x : KernelSpace n) :
    fderiv ℝ (fderiv ℝ (fun y => u (y+a))) x=fderiv ℝ (fderiv ℝ u) (x+a) := by
  have he : fderiv ℝ (fun y => u (y+a))=fun y => fderiv ℝ u (y+a) :=
    funext (fun y => fderiv_comp_add_right a)
  rw [he,fderiv_comp_add_right]

lemma fderiv_comp_dilate_translate {u : KernelSpace n → ℝ} (hu : Differentiable ℝ u)
    (a x : KernelSpace n) (r : ℝ) :
    fderiv ℝ (fun y => u (r • y+a)) x=r • fderiv ℝ u (r • x+a) := by
  let v := fun y => u (y+a)
  have hv : Differentiable ℝ v := hu.comp (differentiable_id.add_const a)
  have he : centeredRescale v 0 r=(fun y => u (r • y+a)) := by funext y; simp [centeredRescale,v]
  have hh := fderiv_centeredRescale hv 0 x r
  rw [he] at hh
  simpa only [sub_zero,v,fderiv_comp_add_right] using hh

lemma secondFrechet_comp_dilate_translate {u : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u)
    (a x : KernelSpace n) (r : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => u (r • y+a))) x=r^2 • fderiv ℝ (fderiv ℝ u) (r • x+a) := by
  let v := fun y => u (y+a)
  have hv : ContDiff ℝ 2 v := hu.comp (contDiff_id.add contDiff_const)
  have he : centeredRescale v 0 r=(fun y => u (r • y+a)) := by funext y; simp [centeredRescale,v]
  have hh := secondFrechet_centeredRescale hv 0 x r
  rw [he] at hh
  simpa only [sub_zero,v,secondFrechet_comp_add_right] using hh

lemma fderiv_comp_dilate_translate_at {u : KernelSpace n → ℝ} (a x : KernelSpace n) (r : ℝ)
    (hu : ContDiffAt ℝ 2 u (r • x+a)) :
    fderiv ℝ (fun y => u (r • y+a)) x=r • fderiv ℝ u (r • x+a) := by
  obtain ⟨v,hv,he⟩ := exists_global_contDiff_eventuallyEq 2 hu
  have hh : (fun y => v (r • y+a)) =ᶠ[𝓝 x] (fun y => u (r • y+a)) :=
    he.comp_tendsto (((continuous_const.smul continuous_id).add continuous_const).tendsto x)
  rw [← hh.fderiv_eq,fderiv_comp_dilate_translate (hv.differentiable (by norm_num)),he.fderiv_eq]

lemma secondFrechet_comp_dilate_translate_at {u : KernelSpace n → ℝ} (a x : KernelSpace n) (r : ℝ)
    (hu : ContDiffAt ℝ 2 u (r • x+a)) :
    fderiv ℝ (fderiv ℝ (fun y => u (r • y+a))) x=r^2 • fderiv ℝ (fderiv ℝ u) (r • x+a) := by
  obtain ⟨v,hv,he⟩ := exists_global_contDiff_eventuallyEq 2 hu
  have hh : (fun y => v (r • y+a)) =ᶠ[𝓝 x] (fun y => u (r • y+a)) :=
    he.comp_tendsto (((continuous_const.smul continuous_id).add continuous_const).tendsto x)
  rw [← hh.fderiv.fderiv_eq,secondFrechet_comp_dilate_translate hv,he.fderiv.fderiv_eq]

lemma kernelLaplacian_comp_dilate_translate_at {u : KernelSpace n → ℝ} (a x : KernelSpace n) (r : ℝ)
    (hu : ContDiffAt ℝ 2 u (r • x+a)) :
    kernelLaplacian (fun y => u (r • y+a)) x=r^2*kernelLaplacian u (r • x+a) := by
  have hc : ContDiffAt ℝ 2 (fun y => u (r • y+a)) x :=
    hu.comp x ((contDiff_const.smul contDiff_id).add contDiff_const).contDiffAt
  rw [kernelLaplacian_eq_trace_at hc,kernelLaplacian_eq_trace_at hu,
    secondFrechet_comp_dilate_translate_at a x r hu]
  simp only [kernelHessianTrace,ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]

lemma dilate_translate_mem_ball (a x : KernelSpace n) {r R : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.ball (0 : KernelSpace n) R) :
    r • x+a ∈ Metric.ball a (r*R) := by
  rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  exact mul_lt_mul_of_pos_left (by simpa only [Metric.mem_ball,dist_zero_right] using hx) hr

end GaussianTilt.MomentMapSchauder
