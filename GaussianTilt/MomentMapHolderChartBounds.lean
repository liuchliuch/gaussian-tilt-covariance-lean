import GaussianTilt.MomentMapHolderChartAlgebra
import GaussianTilt.MomentMapSchauderCompactHolder

/-! # Fixed smooth-chart bounds and actual Hölder composition constants -/
noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace GaussianTilt.HolderSpace
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

structure SmoothChartBounds (ψ : E → F) (T : Set E) (α K : ℝ) : Prop where
  nonneg : 0 ≤ K
  first_bound : ∀ x ∈ T, ‖fderiv ℝ ψ x‖ ≤ K
  second_bound : ∀ x ∈ T, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ K
  first_holder : ∀ x ∈ T, ∀ y ∈ T, ‖fderiv ℝ ψ x-fderiv ℝ ψ y‖ ≤ K*‖x-y‖^α
  second_holder : ∀ x ∈ T, ∀ y ∈ T,
    ‖fderiv ℝ (fderiv ℝ ψ) x-fderiv ℝ (fderiv ℝ ψ) y‖ ≤ K*‖x-y‖^α
  lipschitz : ∀ x ∈ T, ∀ y ∈ T, ‖ψ x-ψ y‖ ≤ K*‖x-y‖

/-- All fixed chart constants are derived from true smooth derivatives and
compact convex geometry, before any unknown jet is supplied. -/
theorem exists_smoothChartBounds {T : Set E} (hTc : IsCompact T) (hT : Convex ℝ T)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (ψ : E → F) (hψ : ContDiff ℝ ∞ ψ) :
    ∃ K : ℝ, 1 ≤ K ∧ SmoothChartBounds ψ T α K := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hD.fderiv_right (by simp)
  obtain ⟨K1,hK1,hD1,hDH⟩ := GaussianTilt.MomentMapSchauder.exists_contDiff_holder_bound_on_compact_convex
    (contDiff_infty.mp hD 1) hTc hT hα hα1
  obtain ⟨K2,hK2,hH1,hHH⟩ := GaussianTilt.MomentMapSchauder.exists_contDiff_holder_bound_on_compact_convex
    (contDiff_infty.mp hH 1) hTc hT hα hα1
  let K := max 1 (max K1 K2)
  have hK : 1 ≤ K := le_max_left _ _
  have hK1K : K1 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK2K : K2 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K,hK,⟨zero_le_one.trans hK,fun x hx => (hD1 x hx).trans hK1K,
    fun x hx => (hH1 x hx).trans hK2K,?_,?_,?_⟩⟩
  · intro x hx y hy
    exact (hDH x hx y hy).trans (mul_le_mul_of_nonneg_right hK1K (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x hx y hy
    exact (hHH x hx y hy).trans (mul_le_mul_of_nonneg_right hK2K (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x hx y hy
    exact hT.norm_image_sub_le_of_norm_fderiv_le (fun _ _ => hψ.differentiable (by simp) _)
      (fun z hz => (hD1 z hz).trans hK1K) hy hx

/-- A genuine source Hölder field composed with the actual Lipschitz chart
has the derived fixed-chart modulus, including boundary points. -/
theorem holder_field_comp_bounds {S : Set F} {T : Set E} {α K N : ℝ}
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (ψ : E → F) (hmap : MapsTo ψ T S)
    (hLip : ∀ x ∈ T, ∀ y ∈ T, ‖ψ x-ψ y‖ ≤ K*‖x-y‖)
    (f : Space S V α) (hfn : ‖f‖ ≤ N) :
    (∀ x ∈ T, ‖extendValue α f (ψ x)‖ ≤ N) ∧
    (∀ x ∈ T, ∀ y ∈ T, ‖extendValue α f (ψ x)-extendValue α f (ψ y)‖ ≤
      (N*K^α)*‖x-y‖^α) := by
  constructor
  · intro x hx
    rw [extendValue_mem α f (hmap hx)]
    exact (norm_value_apply_le S V α f ⟨ψ x,hmap hx⟩).trans hfn
  · intro x hx y hy
    rw [extendValue_mem α f (hmap hx),extendValue_mem α f (hmap hy)]
    have hh := norm_value_sub_le S V α f ⟨ψ x,hmap hx⟩ ⟨ψ y,hmap hy⟩
    simp only [Subtype.dist_eq,dist_eq_norm] at hh
    have hp := Real.rpow_le_rpow (norm_nonneg (ψ x-ψ y)) (hLip x hx y hy) hα
    rw [Real.mul_rpow hK (norm_nonneg _)] at hp
    exact hh.trans ((mul_le_mul hfn hp (Real.rpow_nonneg (norm_nonneg _) _) hN).trans_eq (by ring))

end GaussianTilt.HolderSpace
