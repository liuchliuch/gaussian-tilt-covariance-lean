import GaussianTilt.MomentMapSchauderHolderAlgebra

/-! # Hölder bounds for actual smooth lower-order jet fields -/
noncomputable section
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every genuinely C¹ field has quantitative supremum and α-Hölder bounds
on a compact convex subset of its open regularity domain. The constants
come from compactness of its actual value and derivative fields. -/
theorem exists_contDiffOn_holder_bound_on_compact_convex
    {f : E → F} {Ω S : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hS : IsCompact S) (hSc : Convex ℝ S) (hsub : S ⊆ Ω)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ (∀ x ∈ S, ‖f x‖ ≤ C) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤ C*‖x-y‖^α) := by
  have hDf : ContinuousOn (fderiv ℝ f) Ω :=
    (hf.fderiv_of_isOpen hΩ (m := 0) (by norm_num)).continuousOn
  obtain ⟨U, hUb⟩ := hS.exists_bound_of_continuousOn (hf.continuousOn.mono hsub)
  obtain ⟨L, hLb⟩ := hS.exists_bound_of_continuousOn (hDf.mono hsub)
  let M := max U 1
  let D := max L 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMb : ∀ x ∈ S, ‖f x‖ ≤ M := fun x hx => (hUb x hx).trans (le_max_left _ _)
  have hDb : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ D := fun x hx => (hLb x hx).trans (le_max_left _ _)
  have hLip : ∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤ D*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hf.contDiffAt (hΩ.mem_nhds (hsub hz))).differentiableAt le_rfl) hDb hSc hy hx
  refine ⟨D+2*M, by positivity, ?_, ?_⟩
  · intro x hx
    exact (hMb x hx).trans (by linarith)
  · simpa only [Real.one_rpow, mul_one] using
      holder_bound_of_sup_and_lipschitz hM.le hD.le hα hα1 zero_lt_one hMb hLip

theorem exists_contDiff_holder_bound_on_compact_convex
    {f : E → F} (hf : ContDiff ℝ 1 f) {S : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ (∀ x ∈ S, ‖f x‖ ≤ C) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤ C*‖x-y‖^α) :=
  exists_contDiffOn_holder_bound_on_compact_convex isOpen_univ hf.contDiffOn hS hSc
    (subset_univ S) hα hα1

end GaussianTilt.MomentMapSchauder
