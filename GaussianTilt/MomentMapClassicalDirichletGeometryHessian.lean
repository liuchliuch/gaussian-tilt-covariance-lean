import GaussianTilt.MomentMapClassicalDirichletGeometryDomains
import GaussianTilt.LetwinConvexity

/-! # Quantitative differential geometry of the constructed domains -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma secondFDeriv_nonneg_of_convex {f : E n → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (x v : E n) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let F := fun t : ℝ => f (x+t • v)
  have hF : ContDiff ℝ 2 F := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hFc : ConvexOn ℝ univ F := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    have hh := hc.2 (mem_univ (x+a • v)) (mem_univ (x+b • v)) hs ht hst
    have he : s • (x+a • v)+t • (x+b • v) = x+(s*a+t*b) • v := by
      have het : t = 1-s := by linarith
      rw [het]
      module
    simpa only [F, he, smul_eq_mul] using hh
  have hmono : Monotone (deriv F) := monotoneOn_univ.mp
    (hFc.monotoneOn_deriv (fun t _ => hF.differentiable (by norm_num) t))
  have hh := hmono.deriv_nonneg (x := (0 : ℝ))
  simpa only [F, GaussianTilt.Letwin.second_deriv_affine_line_comp hf,
    zero_smul, add_zero] using hh

lemma secondFDeriv_norm_sq (x v : E n) :
    fderiv ℝ (fderiv ℝ (fun y : E n => ‖y‖^2)) x v v = 2 * ‖v‖^2 := by
  have he : fderiv ℝ (fun y : E n => ‖y‖^2) = fun y => (2 : ℝ) • innerSL ℝ y := by
    funext y
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv
  rw [he]
  have hd := ((innerSL ℝ : E n →L[ℝ] E n →L[ℝ] ℝ).hasFDerivAt (x := x)).const_smul (2 : ℝ)
  have hd' : HasFDerivAt (fun y : E n => (2 : ℝ) • innerSL ℝ y) ((2 : ℝ) • innerSL ℝ) x := hd
  rw [hd'.fderiv]
  simp [real_inner_self_eq_norm_sq]

/-- A strong convexity constant is a genuine lower Hessian eigenvalue bound. -/
theorem secondFDeriv_ge_of_stronglyConvex {f : E n → ℝ}
    (hf : ContDiff ℝ 2 f) {κ : ℝ} (hc : StrongConvexOn univ κ f)
    (x v : E n) : κ * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let q := fun y : E n => κ/2 * ‖y‖^2
  have hq : ContDiff ℝ 2 q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hnonneg := secondFDeriv_nonneg_of_convex (hf.sub hq)
    (strongConvexOn_iff_convex.mp hc) x v
  have hd := hf.differentiable (by norm_num)
  have hqd := hq.differentiable (by norm_num)
  have hDf := (hf.fderiv_right (m:=1) (by norm_num)).differentiable le_rfl
  have hDq := (hq.fderiv_right (m:=1) (by norm_num)).differentiable le_rfl
  have he : fderiv ℝ (fun y => f y-q y) = fun y => fderiv ℝ f y-fderiv ℝ q y := by
    funext y
    exact fderiv_fun_sub (hd y) (hqd y)
  rw [he, fderiv_fun_sub (hDf x) (hDq x)] at hnonneg
  have hqn : fderiv ℝ (fderiv ℝ q) x v v = κ * ‖v‖^2 := by
    have heq : fderiv ℝ q = fun y => (κ/2) • fderiv ℝ (fun z : E n => ‖z‖^2) y := by
      funext y
      exact fderiv_const_mul ((contDiff_norm_sq ℝ : ContDiff ℝ 2 (fun z : E n => ‖z‖^2)).differentiable (by norm_num) y) _
    have hDD := ((contDiff_norm_sq ℝ : ContDiff ℝ 2 (fun z : E n => ‖z‖^2)).fderiv_right
      (m:=1) (by norm_num)).differentiable le_rfl x
    rw [heq, fderiv_fun_const_smul hDD (κ/2)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, secondFDeriv_norm_sq]
    ring
  simp only [ContinuousLinearMap.sub_apply, hqn] at hnonneg
  linarith

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

lemma hessian_lower (x v : E n) :
    d.modulus * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ d.defining) x v v :=
  secondFDeriv_ge_of_stronglyConvex (contDiff_infty.mp d.smooth 2) d.strongly_convex x v

lemma hessian_positive (x : E n) {v : E n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ d.defining) x v v :=
  (mul_pos d.modulus_pos (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (d.hessian_lower x v)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
