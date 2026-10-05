import GaussianTilt.MomentMapHolderCompactness
import GaussianTilt.MomentMapHolderDerivatives

/-! # Genuine differentiability gain from uniform Hölder derivative bounds

Compactness extracts an actual uniform derivative limit. The fundamental
uniform-limit differentiation theorem identifies it with the derivative
of the pointwise function limit. No differentiability of the limit is assumed.
-/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

lemma tendstoUniformlyOn_extendValue {S : Set E} {α : ℝ}
    {D : ℕ → Space S F α} {G : Space S F α}
    (h : Tendsto (fun k => value S F α (D k)) atTop (𝓝 (value S F α G))) :
    TendstoUniformlyOn (fun k => extendValue α (D k)) (extendValue α G) atTop S := by
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with k hk x hx
  simpa only [extendValue_mem α _ hx] using hk ⟨x, hx⟩

/-- Full actual C¹,α regularity of the limit, with its quantitative bound,
from pointwise function convergence and bounded Hölder derivative fields. -/
theorem contDiffOn_one_of_holder_derivative_bounds
    {S : Set E} (hS : IsCompact S) {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (f : ℕ → E → F) (D : ℕ → E → E →L[ℝ] F) (g : E → F)
    (hDc : ∀ k, ContinuousOn (D k) S)
    (hDn : ∀ k x, x ∈ S → ‖D k x‖ ≤ C)
    (hDH : ∀ k x, x ∈ S → ∀ y, y ∈ S → ‖D k x - D k y‖ ≤ C * dist x y ^ α)
    (hf : ∀ k x, x ∈ interior S → HasFDerivAt (f k) (D k x) x)
    (hfg : ∀ x, x ∈ interior S → Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ContDiffOn ℝ 1 g (interior S) ∧
      (∀ x ∈ interior S, ‖fderiv ℝ g x‖ ≤ C) ∧
      (∀ x ∈ interior S, ∀ y ∈ interior S,
        ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ C * dist x y ^ α) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let b : ℕ → (S →ᵇ (E →L[ℝ] F)) := fun k =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x : S => D k x)
      (continuousOn_iff_continuous_restrict.mp (hDc k)) C (fun x => hDn k x x.2)
  have hHb : ∀ k x y, ‖b k x - b k y‖ ≤ C * dist x y ^ α := by
    intro k x y
    exact hDH k x x.2 y y.2
  let d : ℕ → Space S (E →L[ℝ] F) α := fun k => ofBounded S (E →L[ℝ] F) α (b k) C (hHb k)
  have hd : ∀ k, ‖d k‖ ≤ C := by
    intro k
    apply (norm_ofBounded_le S (E →L[ℝ] F) α (b k) hC (hHb k)).trans
    exact max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hC _) le_rfl
  obtain ⟨G, hG, φ, hφ, ht⟩ := exists_uniformly_convergent_subseq S (E →L[ℝ] F) hα hC d hd
  have hDu := (tendstoUniformlyOn_extendValue ht).mono interior_subset
  have hder : ∀ x ∈ interior S, HasFDerivAt g (extendValue α G x) x := by
    intro x hx
    apply hasFDerivAt_of_tendstoUniformlyOn isOpen_interior hDu
    · intro k y hy
      rw [extendValue_mem α _ (interior_subset hy)]
      exact hf (φ k) y hy
    · intro y hy
      exact (hfg y hy).comp hφ.tendsto_atTop
    · exact hx
  refine ⟨?_, ?_, ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    refine ⟨fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact ((continuousOn_extendValue α G).mono interior_subset).congr
        (fun x hx => (hder x hx).fderiv)
  · intro x hx
    rw [(hder x hx).fderiv, extendValue_mem α _ (interior_subset hx)]
    exact (norm_value_apply_le S (E →L[ℝ] F) α G _).trans hG
  · intro x hx y hy
    rw [(hder x hx).fderiv, (hder y hy).fderiv,
      extendValue_mem α _ (interior_subset hx), extendValue_mem α _ (interior_subset hy)]
    exact (norm_value_sub_le S (E →L[ℝ] F) α G _ _).trans
      (mul_le_mul_of_nonneg_right hG (Real.rpow_nonneg dist_nonneg _))

end GaussianTilt.HolderSpace
