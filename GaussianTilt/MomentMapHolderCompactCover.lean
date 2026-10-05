import Mathlib

/-! # Uniform local-to-global Hölder bounds from an actual compact cover

The finite cover and Lebesgue radius are constructed before every member
of the admissible family. No third derivative or boundary approach
hypothesis is used: only the genuine local pairwise Hölder estimates.
-/
noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped Topology
namespace GaussianTilt.HolderSpace
variable {X F Γ : Type*} [MetricSpace X] [NormedAddCommGroup F]

/-- Compact local Schauder patches provide genuine global supremum and
Hölder bounds uniformly for an arbitrary admissible family. -/
theorem uniform_holder_of_compact_local_bounds
    {S : Set X} (hS : IsCompact S) {α : ℝ} (hα : 0 ≤ α)
    (f : Γ → X → F) (P : Γ → Prop) (M : Γ → ℝ)
    (hM : ∀ g, P g → 0 ≤ M g)
    (hlocal : ∀ a ∈ S, ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ g, P g →
      (∀ x ∈ S, dist x a < r → ‖f g x‖ ≤ C*M g) ∧
      (∀ x ∈ S, dist x a < r → ∀ y ∈ S, dist y a < r →
        ‖f g x-f g y‖ ≤ C*M g*dist x y^α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, P g →
      (∀ x ∈ S, ‖f g x‖ ≤ C*M g) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖f g x-f g y‖ ≤ C*M g*dist x y^α) := by
  classical
  choose r K hr hK hloc using fun a : S => hlocal a a.2
  let U : S → Set X := fun a => Metric.ball a (r a)
  have hU : ∀ a, IsOpen (U a) := fun _ => Metric.isOpen_ball
  have hcover : S ⊆ ⋃ a : S, U a := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, Metric.mem_ball_self (hr ⟨x,hx⟩)⟩
  obtain ⟨I, hI⟩ := hS.elim_finite_subcover U hU hcover
  let J := {a : S // a ∈ I}
  have hcoverJ : S ⊆ ⋃ a : J, U a.1 := by
    intro x hx
    have hh := hI hx
    simp only [mem_iUnion] at hh
    obtain ⟨a, ha, hxa⟩ := hh
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,hxa⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric hS (fun a : J => hU a.1) hcoverJ
  let B := ∑ a ∈ I, K a
  have hB : 0 ≤ B := Finset.sum_nonneg (fun a _ => hK a)
  have hKB (a : J) : K a.1 ≤ B := Finset.single_le_sum (fun b _ => hK b) a.2
  have hsup (g : Γ) (hg : P g) (x : X) (hx : x ∈ S) : ‖f g x‖ ≤ B*M g := by
    obtain ⟨a,ha⟩ := hLeb x hx
    have hxa : dist x (a.1 : X) < r a.1 := ha (Metric.mem_ball_self hδ)
    exact ((hloc a.1 g hg).1 x hx hxa).trans (mul_le_mul_of_nonneg_right (hKB a) (hM g hg))
  let C := max B (2*B/δ^α)
  have hC : 0 ≤ C := hB.trans (le_max_left _ _)
  have hδpow : 0 < δ^α := Real.rpow_pos_of_pos hδ _
  refine ⟨C,hC,?_⟩
  intro g hg
  refine ⟨fun x hx => (hsup g hg x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hM g hg)), ?_⟩
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · obtain ⟨a,ha⟩ := hLeb x hx
    have hxa : dist x (a.1 : X) < r a.1 := ha (Metric.mem_ball_self hδ)
    have hya : dist y (a.1 : X) < r a.1 := ha (by simpa only [Metric.mem_ball,dist_comm] using hxy)
    have hh := (hloc a.1 g hg).2 x hx hxa y hy hya
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((hKB a).trans (le_max_left _ _)) (hM g hg))
      (Real.rpow_nonneg dist_nonneg _))
  · have hnorm : ‖f g x-f g y‖ ≤ 2*B*M g :=
      (norm_sub_le _ _).trans (by linarith [hsup g hg x hx,hsup g hg y hy])
    have hp : δ^α ≤ dist x y^α := Real.rpow_le_rpow hδ.le (le_of_not_gt hxy) hα
    have hscale : 2*B*M g ≤ (2*B/δ^α)*M g*dist x y^α := by
      have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg (div_nonneg (show 0 ≤ 2*B by positivity) hδpow.le) (hM g hg))
      have he : ((2*B/δ^α)*M g)*δ^α = 2*B*M g := by field_simp
      rwa [he] at hh
    exact hnorm.trans (hscale.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hM g hg))
      (Real.rpow_nonneg dist_nonneg _)))

end GaussianTilt.HolderSpace
