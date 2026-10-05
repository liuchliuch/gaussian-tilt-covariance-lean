import GaussianTilt.MomentMapHolderSpace

/-! # Actual bounded scalar Hölder extension

The infimum formula constructs a Hölder extension with the same modulus.
Clipping above retains the original supremum bound. No extension theorem
is supplied as a premise.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.HolderSpace
variable {X : Type*} [MetricSpace X]

lemma dist_rpow_triangle {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (x y z : X) :
    dist x z ^ α ≤ dist x y ^ α + dist y z ^ α :=
  (Real.rpow_le_rpow dist_nonneg (dist_triangle x y z) hα).trans
    (Real.rpow_add_le_add_rpow dist_nonneg dist_nonneg hα hα1)

lemma continuous_of_holder_bound {g : X → ℝ} {α H : ℝ} (hα : 0 < α)
    (hg : ∀ x y, |g x - g y| ≤ H * dist x y ^ α) : Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun y : X => H * dist y x ^ α) (𝓝 x) (𝓝 0) := by
    convert (continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_id.dist continuous_const))).tendsto x using 1
    simp [Real.zero_rpow hα.ne']
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => by simpa [Real.norm_eq_abs] using hg y x) ht

/-- An actual bounded scalar Hölder extension, with unchanged supremum
and Hölder constants. The source can be any nonempty subset. -/
theorem exists_bounded_holder_extension {S : Set X} (hS : S.Nonempty)
    {α C H : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (f : S → ℝ) (hb : ∀ x, |f x| ≤ C)
    (hh : ∀ x y, |f x - f y| ≤ H * dist x y ^ α) :
    ∃ g : X → ℝ, Continuous g ∧ (∀ x : S, g x = f x) ∧
      (∀ x, |g x| ≤ C) ∧ (∀ x y, |g x - g y| ≤ H * dist x y ^ α) := by
  letI : Nonempty S := hS.to_subtype
  let e : X → ℝ := fun x => ⨅ y : S, f y + H * dist x y ^ α
  have hbelow (x : X) : BddBelow (range fun y : S => f y + H * dist x y ^ α) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨y, rfl⟩
    have hy := (abs_le.mp (hb y)).1
    exact hy.trans (le_add_of_nonneg_right (mul_nonneg hH (Real.rpow_nonneg dist_nonneg _)))
  have helow (x : X) : -C ≤ e x := by
    apply le_ciInf
    intro y
    exact ((abs_le.mp (hb y)).1).trans
      (le_add_of_nonneg_right (mul_nonneg hH (Real.rpow_nonneg dist_nonneg _)))
  have heq (x : S) : e x = f x := by
    apply le_antisymm
    · simpa only [dist_self, Real.zero_rpow hα.ne', mul_zero, add_zero] using ciInf_le (hbelow x) x
    · apply le_ciInf
      intro y
      have ht := (le_abs_self (f x - f y)).trans (hh x y)
      change f x - f y ≤ H * dist (x : X) y ^ α at ht
      linarith
  have hstep (x y : X) : e x - e y ≤ H * dist x y ^ α := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
    apply le_ciInf
    intro z
    have hez : e x ≤ f z + H * dist x z ^ α := ciInf_le (hbelow x) z
    have hd := mul_le_mul_of_nonneg_left (dist_rpow_triangle hα.le hα1 x y z) hH
    linarith
  have heholder (x y : X) : |e x - e y| ≤ H * dist x y ^ α := by
    apply abs_le.mpr
    constructor
    · have ht := hstep y x
      rw [dist_comm y x] at ht
      linarith
    · exact hstep x y
  let g : X → ℝ := fun x => min C (e x)
  have hgh (x y : X) : |g x - g y| ≤ H * dist x y ^ α := by
    exact (abs_min_sub_min_le_max C (e x) C (e y)).trans (by
      simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (e x - e y))] using heholder x y)
  refine ⟨g, continuous_of_holder_bound hα hgh, ?_, ?_, hgh⟩
  · intro x
    simp only [g, heq, min_eq_right (abs_le.mp (hb x)).2]
  · intro x
    exact abs_le.mpr ⟨le_min (by linarith) (helow x), min_le_left _ _⟩

end GaussianTilt.HolderSpace
