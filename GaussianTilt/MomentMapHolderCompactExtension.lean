import GaussianTilt.MomentMapHolderExtension

/-! # Compactly supported extension of the actual Hölder Banach data

A one-Lipschitz radial cutoff is enough: no smoothness of the forcing is
asserted. Multiplication preserves its genuine Hölder exponent.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.HolderSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def holderExtensionCutoff (R : ℝ) (x : E) : ℝ := max 0 (min 1 (R + 1 - ‖x‖))

lemma holderExtensionCutoff_bounds (R : ℝ) (x : E) :
    0 ≤ holderExtensionCutoff R x ∧ holderExtensionCutoff R x ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma holderExtensionCutoff_eq_one {R : ℝ} {x : E} (hx : ‖x‖ ≤ R) :
    holderExtensionCutoff R x = 1 := by
  simp only [holderExtensionCutoff, min_eq_left (show 1 ≤ R + 1 - ‖x‖ by linarith), max_eq_right zero_le_one]

lemma holderExtensionCutoff_eq_zero {R : ℝ} {x : E} (hx : R + 1 ≤ ‖x‖) :
    holderExtensionCutoff R x = 0 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

lemma holderExtensionCutoff_lipschitz (R : ℝ) (x y : E) :
    |holderExtensionCutoff R x - holderExtensionCutoff R y| ≤ dist x y := by
  calc
    _ ≤ |min 1 (R + 1 - ‖x‖) - min 1 (R + 1 - ‖y‖)| := by
      simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (min 1 (R + 1 - ‖x‖) - min 1 (R + 1 - ‖y‖)))] using
        abs_max_sub_max_le_max 0 (min 1 (R + 1 - ‖x‖)) 0 (min 1 (R + 1 - ‖y‖))
    _ ≤ |(R + 1 - ‖x‖) - (R + 1 - ‖y‖)| := by
      simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg ((R + 1 - ‖x‖) - (R + 1 - ‖y‖)))] using
        abs_min_sub_min_le_max 1 (R + 1 - ‖x‖) 1 (R + 1 - ‖y‖)
    _ = |‖x‖ - ‖y‖| := by
      rw [show (R + 1 - ‖x‖) - (R + 1 - ‖y‖) = ‖y‖ - ‖x‖ by ring, abs_sub_comm]
    _ ≤ dist x y := by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y

lemma holderExtensionCutoff_holder {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (R : ℝ) (x y : E) :
    |holderExtensionCutoff R x - holderExtensionCutoff R y| ≤ dist x y ^ α := by
  by_cases hd : dist x y ≤ 1
  · exact (holderExtensionCutoff_lipschitz R x y).trans
      (Real.self_le_rpow_of_le_one dist_nonneg hd hα1)
  · have hb : |holderExtensionCutoff R x - holderExtensionCutoff R y| ≤ 1 := by
      have hx := holderExtensionCutoff_bounds R x
      have hy := holderExtensionCutoff_bounds R y
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact hb.trans (Real.one_le_rpow (le_of_not_ge hd) hα)

/-- Every actual closed-domain Hölder function has an actual compact Hölder
extension. The extension has supremum at most the original norm and Hölder
constant at most twice that norm, uniformly over the datum. -/
theorem exists_compact_holder_extension {S : Set E} (hSc : IsCompact S)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (f : Space S ℝ α) :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ x : S, g x = value S ℝ α f x) ∧
      (∀ x, |g x| ≤ ‖f‖) ∧
      (∀ x y, |g x - g y| ≤ (2 * ‖f‖) * dist x y ^ α) := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨e, hec, heq, heb, heh⟩ := exists_bounded_holder_extension hS hα hα1
      (norm_nonneg f) (norm_nonneg f) (value S ℝ α f)
      (fun x => by simpa only [Real.norm_eq_abs] using norm_value_apply_le S ℝ α f x)
      (fun x y => by simpa only [Real.norm_eq_abs] using norm_value_sub_le S ℝ α f x y)
    obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall (0 : E)
    let χ : E → ℝ := holderExtensionCutoff R
    let g : E → ℝ := fun x => χ x * e x
    have hχb (x : E) : |χ x| ≤ 1 := by
      rw [abs_of_nonneg (holderExtensionCutoff_bounds R x).1]
      exact (holderExtensionCutoff_bounds R x).2
    have hgh (x y : E) : |g x - g y| ≤ (2 * ‖f‖) * dist x y ^ α := by
      calc
        _ = |χ x * (e x - e y) + (χ x - χ y) * e y| := by congr 1; dsimp [g]; ring
        _ ≤ |χ x| * |e x - e y| + |χ x - χ y| * |e y| := by
          simpa only [abs_mul] using abs_add_le (χ x * (e x - e y)) ((χ x - χ y) * e y)
        _ ≤ 1 * (‖f‖ * dist x y ^ α) + (dist x y ^ α) * ‖f‖ := by
          gcongr
          · exact hχb x
          · exact heh x y
          · exact holderExtensionCutoff_holder hα.le hα1 R x y
          · exact heb y
        _ = _ := by ring
    refine ⟨g, continuous_of_holder_bound hα hgh, ?_, ?_, ?_, hgh⟩
    · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (R + 1))
      intro x hx
      by_contra hn
      have hz : χ x = 0 := holderExtensionCutoff_eq_zero (by
        have hh : R + 1 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
        exact hh.le)
      exact hx (by simp only [g, hz, zero_mul])
    · intro x
      have hx : ‖(x : E)‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hR x.2
      simp only [g, χ, holderExtensionCutoff_eq_one hx, one_mul, heq]
    · intro x
      calc
        |g x| = |χ x| * |e x| := abs_mul _ _
        _ ≤ 1 * ‖f‖ := mul_le_mul (hχb x) (heb x) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    refine ⟨fun _ => 0, continuous_const, HasCompactSupport.zero, ?_, ?_, ?_⟩
    · intro x; exact False.elim (by simpa only [he, mem_empty_iff_false] using x.2)
    · intro x; simpa using norm_nonneg f
    · intro x y; simpa only [sub_self, abs_zero] using
        mul_nonneg (by positivity : 0 ≤ 2 * ‖f‖) (Real.rpow_nonneg dist_nonneg α)

end GaussianTilt.HolderSpace
