import GaussianTilt.MomentMapSchauderSourceUniform
import GaussianTilt.MomentMapSchauderDifferenceLimit

/-! # Actual C³,α source gain from the genuine finite-difference PDE -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma contDiffOn_clm_of_unit_apply {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → E →L[ℝ] F} {S : Set G} {k : WithTop ℕ∞}
    (hf : ∀ e : E, ‖e‖ ≤ 1 → ContDiffOn ℝ k (fun x => f x e) S) :
    ContDiffOn ℝ k f S := by
  apply contDiffOn_clm_apply.mpr
  intro e
  by_cases he : e=0
  · simpa only [he, map_zero] using (contDiffOn_const : ContDiffOn ℝ k (fun _ : G => (0 : F)) S)
  · have hn : ‖(‖e‖⁻¹ : ℝ) • e‖ ≤ 1 := (norm_smul_inv_norm (𝕜 := ℝ) he).le
    have hh := (hf ((‖e‖⁻¹ : ℝ) • e) hn).const_smul ‖e‖
    convert hh using 1
    funext x
    rw [map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he), one_smul]

lemma fderiv_clm_apply_const_apply {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → E →L[ℝ] F} {x : G} (hf : DifferentiableAt ℝ f x) (v : G) (e : E) :
    fderiv ℝ (fun y => f y e) x v=fderiv ℝ f x v e := by
  rw [fderiv_clm_apply hf (differentiableAt_const e)]
  simp

/-- Unit-direction C¹,α estimates reconstruct the genuine derivative of
a continuous-linear-map-valued field, with the same operator-norm bounds. -/
theorem clm_field_derivative_bounds {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → E →L[ℝ] F} {S : Set G} (hS : IsOpen S) {C α : ℝ} (hC : 0 ≤ C)
    (hf : ∀ e : E, ‖e‖ ≤ 1 → ContDiffOn ℝ 1 (fun x => f x e) S)
    (hb : ∀ e : E, ‖e‖ ≤ 1 → ∀ x ∈ S, ‖fderiv ℝ (fun y => f y e) x‖ ≤ C)
    (hh : ∀ e : E, ‖e‖ ≤ 1 → ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (fun z => f z e) x-fderiv ℝ (fun z => f z e) y‖ ≤ C*‖x-y‖^α) :
    ContDiffOn ℝ 1 f S ∧ (∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ C) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ C*‖x-y‖^α) := by
  have hfc := contDiffOn_clm_of_unit_apply hf
  have hfd : ∀ x ∈ S, DifferentiableAt ℝ f x := fun x hx =>
    (hfc.contDiffAt (hS.mem_nhds hx)).differentiableAt le_rfl
  refine ⟨hfc, ?_, ?_⟩
  · intro x hx
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
    intro v hv
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
    intro e he
    have hn := (fderiv ℝ (fun y => f y e) x).le_opNorm v
    rw [fderiv_clm_apply_const_apply (hfd x hx), hv, mul_one] at hn
    exact hn.trans (hb e he.le x hx)
  · intro x hx y hy
    have hp : 0 ≤ C*‖x-y‖^α := by positivity
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hp
    intro v hv
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hp
    intro e he
    have hn := (fderiv ℝ (fun z => f z e) x-fderiv ℝ (fun z => f z e) y).le_opNorm v
    simp only [ContinuousLinearMap.sub_apply, fderiv_clm_apply_const_apply (hfd x hx),
      fderiv_clm_apply_const_apply (hfd y hy), hv, mul_one] at hn ⊢
    exact hn.trans (hh e he.le x hx y hy)

/-- The first genuine Schauder bootstrap gain. No third derivative,
classical linear solvability, or source ellipticity modulus is assumed. -/
theorem exists_source_third_order_holder [NeZero n]
    {φ g : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 1 g)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det=g x)
    (a : KernelSpace n) {R Hφ Hg α : ℝ} (hR : 0 < R)
    (hHφ : 0 ≤ Hφ) (hHg : 0 ≤ Hg) (hα : 0 < α) (hα1 : α < 1)
    (hφH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ Hφ*‖x-y‖^α)
    (hgH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ g x-fderiv ℝ g y‖ ≤ Hg*‖x-y‖^α) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R ∧ 0 < C ∧ ContDiffOn ℝ 3 φ (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y‖ ≤ C*‖x-y‖^α) := by
  obtain ⟨r, C, hr, hrR, hC, hq⟩ :=
    exists_uniform_source_difference_schauder hφ hg hpos hMA a hR hHφ hHg hα hα1 hφH hgH
  let S := Metric.closedBall a (r/2)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hsub : S ⊆ Metric.ball a r := Metric.closedBall_subset_ball (by linarith)
  have hint : interior S=Metric.ball a (r/2) := interior_closedBall _ (by linarith : (r/2 : ℝ) ≠ 0)
  have hDφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hgain (e : KernelSpace n) (he : ‖e‖ ≤ 1) :=
    contDiffOn_fderiv_apply_of_quotient_derivative_bounds hDφ hS hα hC.le hR e
      (fun s hs hsb x hx => by
        rw [← secondFrechet_vectorDifferenceQuotient hφ]
        exact (hq e he s hs hsb).1 x (hsub hx))
      (fun s hs hsb x hx y hy => by
        rw [← secondFrechet_vectorDifferenceQuotient hφ, ← secondFrechet_vectorDifferenceQuotient hφ]
        exact (hq e he s hs hsb).2 x (hsub hx) y (hsub hy))
  have hg' := clm_field_derivative_bounds (f := fderiv ℝ (fderiv ℝ φ))
    isOpen_interior hC.le (fun e he => (hgain e he).1)
    (fun e he => (hgain e he).2.1) (fun e he => (hgain e he).2.2)
  have hDφ₂ : ContDiffOn ℝ 2 (fderiv ℝ φ) (interior S) := by
    rw [show (2 : WithTop ℕ∞)=1+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    exact ⟨(hDφ.differentiable le_rfl).differentiableOn, by simp, hg'.1⟩
  have hφ₃ : ContDiffOn ℝ 3 φ (interior S) := by
    rw [show (3 : WithTop ℕ∞)=2+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    exact ⟨(hφ.differentiable (by norm_num)).differentiableOn, by simp, hDφ₂⟩
  refine ⟨r/2, C, by linarith, by linarith, hC, ?_, ?_, ?_⟩
  · simpa only [hint] using hφ₃
  · simpa only [hint] using hg'.2.1
  · simpa only [hint] using hg'.2.2

/-- Reusable actual third-order gain from proved step-uniform Hessian
bounds, for both nonlinear source quotients and differentiated linear PDEs. -/
theorem contDiffOn_three_of_uniform_second_difference_bounds [NeZero n]
    {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (a : KernelSpace n)
    {r R C α : ℝ} (hr : 0 < r) (hR : 0 < R) (hC : 0 ≤ C) (hα : 0 < α)
    (hq : ∀ e : KernelSpace n, ‖e‖ ≤ 1 → ∀ s : ℝ, s ≠ 0 → |s| ≤ R →
      (∀ x ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient φ (s • e) s)) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient φ (s • e) s)) x-
          fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient φ (s • e) s)) y‖ ≤ C*‖x-y‖^α)) :
    ContDiffOn ℝ 3 φ (Metric.ball a (r/2)) ∧
      (∀ x ∈ Metric.ball a (r/2), ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a (r/2), ∀ y ∈ Metric.ball a (r/2),
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y‖ ≤ C*‖x-y‖^α) := by
  let S := Metric.closedBall a (r/2)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hsub : S ⊆ Metric.ball a r := Metric.closedBall_subset_ball (by linarith)
  have hint : interior S=Metric.ball a (r/2) := interior_closedBall _ (by linarith : (r/2 : ℝ) ≠ 0)
  have hDφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hgain (e : KernelSpace n) (he : ‖e‖ ≤ 1) :=
    contDiffOn_fderiv_apply_of_quotient_derivative_bounds hDφ hS hα hC hR e
      (fun s hs hsb x hx => by
        rw [← secondFrechet_vectorDifferenceQuotient hφ]
        exact (hq e he s hs hsb).1 x (hsub hx))
      (fun s hs hsb x hx y hy => by
        rw [← secondFrechet_vectorDifferenceQuotient hφ, ← secondFrechet_vectorDifferenceQuotient hφ]
        exact (hq e he s hs hsb).2 x (hsub hx) y (hsub hy))
  have hg' := clm_field_derivative_bounds (f := fderiv ℝ (fderiv ℝ φ))
    isOpen_interior hC (fun e he => (hgain e he).1)
    (fun e he => (hgain e he).2.1) (fun e he => (hgain e he).2.2)
  have hDφ₂ : ContDiffOn ℝ 2 (fderiv ℝ φ) (interior S) := by
    rw [show (2 : WithTop ℕ∞)=1+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    exact ⟨(hDφ.differentiable le_rfl).differentiableOn, by simp, hg'.1⟩
  have hφ₃ : ContDiffOn ℝ 3 φ (interior S) := by
    rw [show (3 : WithTop ℕ∞)=2+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    exact ⟨(hφ.differentiable (by norm_num)).differentiableOn, by simp, hDφ₂⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hint] using hφ₃
  · simpa only [hint] using hg'.2.1
  · simpa only [hint] using hg'.2.2

end GaussianTilt.MomentMapSchauder
