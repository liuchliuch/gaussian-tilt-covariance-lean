import GaussianTilt.LowerScales
import GaussianTilt.UniformModerate

/-! # From uniform absolute slice estimates to the local ratio envelope -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GaussianTilt.UniformModerate

lemma profile_exp_lower {r s : ℝ} (hr : 0 ≤ r) (hs : s ∈ Icc (0 : ℝ) 2) :
    Real.exp (-(5 / 2 : ℝ) * r) * Real.exp (-10 * r * s) ≤
      Real.exp (-(5 / 2 : ℝ) * r * (1 + s) ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg hr (mul_nonneg hs.1 (show 0 ≤ 2 - s by linarith [hs.2]))
  nlinarith

lemma profile_exp_upper {r s : ℝ} (hr : 0 ≤ r) :
    Real.exp (-(5 / 2 : ℝ) * r * (1 + s) ^ 2) ≤
      Real.exp (-(5 / 2 : ℝ) * r) * Real.exp (-5 * r * s) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hr (sq_nonneg s)]

lemma local_ratio_of_absolute {f : ℝ → ℝ} {A r c C : ℝ}
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hc : 0 < c) (hC : 0 < C)
    (habs : ∀ s ∈ Icc (0 : ℝ) 2,
      c * A * Real.exp (-(5 / 2 : ℝ) * r * (1 + s) ^ 2) ≤ f s ∧
      f s ≤ C * A * Real.exp (-(5 / 2 : ℝ) * r * (1 + s) ^ 2)) :
    ∀ s ∈ Icc (0 : ℝ) 2,
      (c / C) * f 0 * Real.exp (-10 * r * s) ≤ f s ∧
      f s ≤ (C / c) * f 0 * Real.exp (-5 * r * s) := by
  have hz := habs 0 (by constructor <;> norm_num)
  simp only [add_zero, one_pow, mul_one] at hz
  intro s hs
  obtain ⟨hl, hu⟩ := habs s hs
  constructor
  · calc
      (c / C) * f 0 * Real.exp (-10 * r * s) ≤
          (c / C) * (C * A * Real.exp (-(5 / 2 : ℝ) * r)) * Real.exp (-10 * r * s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz.2 (by positivity)) (Real.exp_nonneg _)
      _ = c * A * (Real.exp (-(5 / 2 : ℝ) * r) * Real.exp (-10 * r * s)) := by field_simp
      _ ≤ c * A * Real.exp (-(5 / 2 : ℝ) * r * (1 + s) ^ 2) :=
        mul_le_mul_of_nonneg_left (profile_exp_lower hr hs) (mul_nonneg hc.le hA)
      _ ≤ f s := hl
  · calc
      f s ≤ C * A * Real.exp (-(5 / 2 : ℝ) * r * (1 + s) ^ 2) := hu
      _ ≤ C * A * (Real.exp (-(5 / 2 : ℝ) * r) * Real.exp (-5 * r * s)) :=
        mul_le_mul_of_nonneg_left (profile_exp_upper hr) (mul_nonneg hC.le hA)
      _ = (C / c) * (c * A * Real.exp (-(5 / 2 : ℝ) * r)) * Real.exp (-5 * r * s) := by field_simp
      _ ≤ (C / c) * f 0 * Real.exp (-5 * r * s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz.1 (by positivity)) (Real.exp_nonneg _)

/-- The local ratio envelope is now proved for the actual cube from the
completed, uniformly specialized moderate-deviation theorem. -/
theorem exists_eventually_localSliceComparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop, LowerScales.LocalSliceComparison d c C 5 10 := by
  obtain ⟨c, C, hc, hC, hbound⟩ := original4_4 (s₀ := 2) (by norm_num)
  refine ⟨c / C, C / c, div_pos hc hC, div_pos hC hc, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with d hd hd0
  unfold LowerScales.LocalSliceComparison
  rw [deviationScale_sq_div hd0]
  exact local_ratio_of_absolute (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _) hc hC hd

end GaussianTilt.UniformModerate
