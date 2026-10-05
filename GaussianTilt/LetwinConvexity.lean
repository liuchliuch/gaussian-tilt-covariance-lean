import GaussianTilt.LetwinPositivity
import GaussianTilt.LetwinBlock

/-! # Convexity from actual second directional derivatives -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace GaussianTilt.Letwin

section SecondDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma deriv_affine_line_comp {f : E → ℝ} (hf : Differentiable ℝ f) (x v : E) (t : ℝ) :
    deriv (fun s : ℝ => f (x + s • v)) t = fderiv ℝ f (x + t • v) v := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using (hasDerivAt_const t x).fun_add ((hasDerivAt_id t).smul_const v)
  exact ((hf _).hasFDerivAt.comp_hasDerivAt t hl).deriv

lemma second_deriv_affine_line_comp {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) (t : ℝ) :
    deriv (deriv (fun s : ℝ => f (x + s • v))) t =
      fderiv ℝ (fderiv ℝ f) (x + t • v) v v := by
  have hd := hf.differentiable (by norm_num)
  have hDD : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have heq : deriv (fun s : ℝ => f (x + s • v)) =
      (fun s => fderiv ℝ f (x + s • v) v) := funext (deriv_affine_line_comp hd x v)
  rw [heq]
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using (hasDerivAt_const t x).fun_add ((hasDerivAt_id t).smul_const v)
  have h := ((hDD _).hasFDerivAt.comp_hasDerivAt t hl).clm_apply (hasDerivAt_const t v)
  simpa using h.deriv

/-- The Hessian criterion on any convex set, including compact sets with
boundary. Smoothness is supplied globally, but Hessian nonnegativity is needed
only on the set itself. -/
theorem convexOn_of_secondFDeriv_nonneg {f : E → ℝ} {K : Set E}
    (hK : Convex ℝ K) (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x ∈ K, ∀ v : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) : ConvexOn ℝ K f := by
  refine ⟨hK, ?_⟩
  intro x hx y hy a b ha hb hab
  let F := fun t : ℝ => f (x + t • (y - x))
  have hF : ContDiff ℝ 2 F := hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ K := by
    have h := hK hx hy (show 0 ≤ 1 - t by linarith [ht.2]) ht.1 (by ring : (1 - t) + t = 1)
    convert h using 1
    module
  have hFc : ConvexOn ℝ (Icc (0 : ℝ) 1) F := by
    apply convexOn_of_deriv2_nonneg' (convex_Icc _ _)
      (hF.differentiable (by norm_num)).differentiableOn
      hF.differentiable_deriv_two.differentiableOn
    intro t ht
    change 0 ≤ deriv (deriv F) t
    rw [second_deriv_affine_line_comp hf x (y - x) t]
    exact hpos _ (hline t ht) _
  have h := hFc.2 (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1) ha hb hab
  have heq : x + b • (y - x) = a • x + b • y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    module
  simpa [F, heq] using h

end SecondDerivative
end GaussianTilt.Letwin
