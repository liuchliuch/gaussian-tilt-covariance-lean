import GaussianTilt.MomentMapHolderCompactCover

/-! # Compact Schauder absorption with independent data and highest coefficients

Patch radii precede the small parameter. The Lebesgue factor multiplies that
parameter alone, rather than a potentially divergent data constant.
-/
noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped Topology
namespace GaussianTilt.HolderSpace
variable {X F Γ : Type*} [MetricSpace X] [NormedAddCommGroup F]

theorem uniform_holder_small_highest_of_compact_local_bounds
    {S : Set X} (hS : IsCompact S) {α : ℝ} (hα : 0 ≤ α)
    (f : Γ → X → F) (P : Γ → Prop) (M Q : Γ → ℝ)
    (hM : ∀ g, P g → 0 ≤ M g) (hQ : ∀ g, P g → 0 ≤ Q g)
    (hlocal : ∀ a ∈ S, ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      0 ≤ C ∧ ∀ g, P g →
      (∀ x ∈ S, dist x a < r → ‖f g x‖ ≤ C*M g+ε*Q g) ∧
      (∀ x ∈ S, dist x a < r → ∀ y ∈ S, dist y a < r →
        ‖f g x-f g y‖ ≤ (C*M g+ε*Q g)*dist x y^α)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ g, P g →
      (∀ x ∈ S, ‖f g x‖ ≤ C*M g+ε*Q g) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖f g x-f g y‖ ≤ (C*M g+ε*Q g)*dist x y^α) := by
  classical
  choose r hr hloc using fun a : S => hlocal a a.2
  let U : S → Set X := fun a => Metric.ball a (r a)
  have hU : ∀ a, IsOpen (U a) := fun _ => Metric.isOpen_ball
  have hcover : S ⊆ ⋃ a : S, U a := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hr ⟨x,hx⟩)⟩
  obtain ⟨I,hI⟩ := hS.elim_finite_subcover U hU hcover
  let J := {a : S // a ∈ I}
  have hcoverJ : S ⊆ ⋃ a : J, U a.1 := by
    intro x hx
    have hh := hI hx
    simp only [mem_iUnion] at hh
    obtain ⟨a,ha,hxa⟩ := hh
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,hxa⟩
  obtain ⟨d,hd,hLeb⟩ := lebesgue_number_lemma_of_metric hS (fun a : J => hU a.1) hcoverJ
  let L : ℝ := max 1 (2/d^α)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hdp : 0 < d^α := Real.rpow_pos_of_pos hd _
  intro ε hε
  let η := ε/L
  have hη : 0 < η := div_pos hε hL
  have hηL : L*η = ε := by dsimp only [η]; field_simp
  have hηε : η ≤ ε := by nlinarith [mul_le_mul_of_nonneg_right hL1 hη.le]
  choose K hK hbound using fun a : S => hloc a η hη
  let B := ∑ a ∈ I, K a
  have hB : 0 ≤ B := Finset.sum_nonneg (fun a _ => hK a)
  have hKB (a : J) : K a.1 ≤ B := Finset.single_le_sum (fun b _ => hK b) a.2
  have hsup (g : Γ) (hg : P g) (x : X) (hx : x ∈ S) :
      ‖f g x‖ ≤ B*M g+η*Q g := by
    obtain ⟨a,ha⟩ := hLeb x hx
    have hxa : dist x (a.1 : X) < r a.1 := ha (Metric.mem_ball_self hd)
    exact ((hbound a.1 g hg).1 x hx hxa).trans
      (add_le_add_right (mul_le_mul_of_nonneg_right (hKB a) (hM g hg)) _)
  refine ⟨L*B,mul_nonneg hL.le hB,?_⟩
  intro g hg
  have htot : B*M g+η*Q g ≤ (L*B)*M g+ε*Q g := by
    have hh := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hB (hM g hg))
    nlinarith [mul_le_mul_of_nonneg_right hηε (hQ g hg)]
  refine ⟨fun x hx => (hsup g hg x hx).trans htot,?_⟩
  intro x hx y hy
  by_cases hxy : dist x y < d
  · obtain ⟨a,ha⟩ := hLeb x hx
    have hxa : dist x (a.1 : X) < r a.1 := ha (Metric.mem_ball_self hd)
    have hya : dist y (a.1 : X) < r a.1 := ha (by simpa only [Metric.mem_ball,dist_comm] using hxy)
    have hh := (hbound a.1 g hg).2 x hx hxa y hy hya
    exact hh.trans (mul_le_mul_of_nonneg_right
      ((add_le_add_right (mul_le_mul_of_nonneg_right (hKB a) (hM g hg)) _).trans htot)
      (Real.rpow_nonneg dist_nonneg _))
  · have hn : ‖f g x-f g y‖ ≤ 2*(B*M g+η*Q g) :=
      (norm_sub_le _ _).trans (by linarith [hsup g hg x hx,hsup g hg y hy])
    have hp : d^α ≤ dist x y^α := Real.rpow_le_rpow hd.le (le_of_not_gt hxy) hα
    have ht0 : 0 ≤ B*M g+η*Q g := add_nonneg (mul_nonneg hB (hM g hg)) (mul_nonneg hη.le (hQ g hg))
    have hscale : 2*(B*M g+η*Q g) ≤ (2/d^α)*(B*M g+η*Q g)*dist x y^α := by
      have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg (div_nonneg (show (0:ℝ) ≤ 2 by norm_num) hdp.le) ht0)
      have he : (2/d^α)*(B*M g+η*Q g)*d^α = 2*(B*M g+η*Q g) := by field_simp
      rwa [he] at hh
    have he : L*(B*M g+η*Q g) = (L*B)*M g+ε*Q g := by rw [mul_add]; rw [← mul_assoc L η, hηL]; ring
    have hcoeff : (2/d^α)*(B*M g+η*Q g) ≤ (L*B)*M g+ε*Q g := by
      rw [← he]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) ht0
    exact hn.trans (hscale.trans (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg dist_nonneg _)))

end GaussianTilt.HolderSpace
