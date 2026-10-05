import GaussianTilt.MomentMapSchauderHolderInterpolation

/-! # Quantitative finite-sum bounds for localized PDE forcing -/
noncomputable section
open Set
open scoped BigOperators
namespace GaussianTilt.MomentMapSchauder

lemma abs_finset_sum_bound {ι : Type*} [Fintype ι] {f : ι → ℝ} {C : ℝ}
    (hf : ∀ i, |f i| ≤ C) : |∑ i, f i| ≤ (Fintype.card ι : ℝ) * C := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum
    (fun i _ => hf i)).trans_eq (by simp))

lemma holder_finite_sum_bound {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]
    {f : ι → E → ℝ} {C α : ℝ}
    (hf : ∀ i x y, |f i x - f i y| ≤ C * ‖x-y‖ ^ α) :
    ∀ x y, |(∑ i, f i x) - ∑ i, f i y| ≤
      ((Fintype.card ι : ℝ) * C) * ‖x-y‖ ^ α := by
  intro x y
  rw [← Finset.sum_sub_distrib]
  exact (abs_finset_sum_bound (fun i => hf i x y)).trans_eq (by ring)

lemma holder_sum_two {E : Type*} [NormedAddCommGroup E] {f g : E → ℝ} {C D α : ℝ}
    (hf : ∀ x y, |f x-f y| ≤ C*‖x-y‖^α)
    (hg : ∀ x y, |g x-g y| ≤ D*‖x-y‖^α) :
    ∀ x y, |(f x+g x)-(f y+g y)| ≤ (C+D)*‖x-y‖^α := by
  intro x y
  have he : (f x+g x)-(f y+g y)=(f x-f y)+(g x-g y) := by ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add (hf x y) (hg x y)).trans_eq (by ring))

lemma holder_const_mul {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} {C α : ℝ}
    (hf : ∀ x y, |f x-f y| ≤ C*‖x-y‖^α) (c : ℝ) :
    ∀ x y, |c*f x-c*f y| ≤ (|c| * C)*‖x-y‖^α := by
  intro x y
  rw [← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg c)).trans_eq (by ring)

end GaussianTilt.MomentMapSchauder
