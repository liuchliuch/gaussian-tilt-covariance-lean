import GaussianTilt.MomentMapSchauderHolderInterpolation
import Mathlib.Analysis.NormedSpace.Multilinear.Basic

/-! # Hölder algebra for actual higher derivative fields

All estimates are operator-norm estimates for finite sums, scalar products,
linear evaluations, and multilinear evaluations. They support the actual
higher-order chain-rule forcing without positing regularity of that forcing.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
open Set
open scoped BigOperators
namespace GaussianTilt.MomentMapSchauder
variable {E F G : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma holder_smul_bound_norm {a : E → ℝ} {f : E → F} {S : Set E}
    {A B HA HB α : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : 0 ≤ HA) (hHB : 0 ≤ HB)
    (hab : ∀ x ∈ S, |a x| ≤ A) (hfb : ∀ x ∈ S, ‖f x‖ ≤ B)
    (haH : ∀ x ∈ S, ∀ y ∈ S, |a x-a y| ≤ HA*‖x-y‖^α)
    (hfH : ∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤ HB*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖a x • f x-a y • f y‖ ≤ (A*HB+HA*B)*‖x-y‖^α := by
  intro x hx y hy
  have he : a x • f x-a y • f y=a x • (f x-f y)+(a x-a y) • f y := by module
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Real.norm_eq_abs]
  exact (add_le_add (mul_le_mul (hab x hx) (hfH x hx y hy) (norm_nonneg _) hA)
    (mul_le_mul (haH x hx y hy) (hfb y hy) (norm_nonneg _) (by positivity))).trans_eq (by ring)

lemma holder_clm_apply_bound {a : E → F →L[ℝ] G} {f : E → F} {S : Set E}
    {A B HA HB α : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : 0 ≤ HA) (hHB : 0 ≤ HB)
    (hab : ∀ x ∈ S, ‖a x‖ ≤ A) (hfb : ∀ x ∈ S, ‖f x‖ ≤ B)
    (haH : ∀ x ∈ S, ∀ y ∈ S, ‖a x-a y‖ ≤ HA*‖x-y‖^α)
    (hfH : ∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤ HB*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖a x (f x)-a y (f y)‖ ≤ (A*HB+HA*B)*‖x-y‖^α := by
  intro x hx y hy
  have he : a x (f x)-a y (f y)=a x (f x-f y)+(a x-a y) (f y) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have hb := add_le_add ((a x).le_opNorm (f x-f y)) ((a x-a y).le_opNorm (f y))
  apply hb.trans
  exact (add_le_add (mul_le_mul (hab x hx) (hfH x hx y hy) (norm_nonneg _) hA)
    (mul_le_mul (haH x hx y hy) (hfb y hy) (norm_nonneg _) (by positivity))).trans_eq (by ring)

lemma holder_finset_sum_norm {ι : Type*} (s : Finset ι) {f : ι → E → F} {S : Set E}
    {C : ι → ℝ} {α : ℝ}
    (hh : ∀ i ∈ s, ∀ x ∈ S, ∀ y ∈ S, ‖f i x-f i y‖ ≤ C i*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖(∑ i ∈ s, f i x)-∑ i ∈ s, f i y‖ ≤ (∑ i ∈ s, C i)*‖x-y‖^α := by
  intro x hx y hy
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hh i hi x hx y hy))

/-- Quantitative evaluation of a genuine multilinear derivative field at
Hölder vector fields. The finite-dimensional input tuple is measured in its
actual supremum norm, avoiding unproved tensor estimates. -/
theorem holder_multilinear_apply_bound {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {a : E → ContinuousMultilinearMap ℝ V F} {v : E → ∀ i, V i} {S : Set E}
    {A B HA HB α : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hHA : 0 ≤ HA) (hHB : 0 ≤ HB)
    (hab : ∀ x ∈ S, ‖a x‖ ≤ A) (hvb : ∀ x ∈ S, ‖v x‖ ≤ B)
    (haH : ∀ x ∈ S, ∀ y ∈ S, ‖a x-a y‖ ≤ HA*‖x-y‖^α)
    (hvH : ∀ x ∈ S, ∀ y ∈ S, ‖v x-v y‖ ≤ HB*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖a x (v x)-a y (v y)‖ ≤
      (A*(Fintype.card ι : ℝ)*B^(Fintype.card ι-1)*HB+HA*B^(Fintype.card ι))*‖x-y‖^α := by
  intro x hx y hy
  have he : a x (v x)-a y (v y)=(a x (v x)-a x (v y))+(a x-a y) (v y) := by
    simp only [ContinuousMultilinearMap.sub_apply]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have hmax : max ‖v x‖ ‖v y‖ ≤ B := max_le (hvb x hx) (hvb y hy)
  have hnear := (a x).norm_image_sub_le (v x) (v y)
  have hn : ‖a x (v x)-a x (v y)‖ ≤
      A*(Fintype.card ι : ℝ)*B^(Fintype.card ι-1)*(HB*‖x-y‖^α) := by
    apply hnear.trans
    gcongr
    · exact hab x hx
    · exact hvH x hx y hy
  have ht : ‖(a x-a y) (v y)‖ ≤ (HA*‖x-y‖^α)*B^(Fintype.card ι) := by
    apply ((a x-a y).le_opNorm (v y)).trans
    apply mul_le_mul (haH x hx y hy) _ (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (by positivity)
    calc
      (∏ i, ‖v y i‖) ≤ ∏ _i : ι, B := Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i _ => (norm_le_pi_norm (v y) i).trans (hvb y hy))
      _ = B^(Fintype.card ι) := by simp
  exact (add_le_add hn ht).trans_eq (by ring)

end GaussianTilt.MomentMapSchauder
