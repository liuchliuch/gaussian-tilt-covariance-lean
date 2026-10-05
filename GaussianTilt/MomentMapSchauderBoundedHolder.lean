import GaussianTilt.MomentMapSchauderCompactHolder

/-! # Compositional bounded Hölder estimates on a fixed set -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open Set
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
variable {E F G : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- A common actual bound for the value and Hölder difference on a set. -/
def BoundedHolderOn (α : ℝ) (f : E → F) (S : Set E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ (∀ x ∈ S, ‖f x‖ ≤ C) ∧
    ∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤ C*‖x-y‖^α

namespace BoundedHolderOn
variable {α : ℝ} {S T : Set E} {f g : E → F}

lemma mono (hf : BoundedHolderOn α f S) (hT : T ⊆ S) : BoundedHolderOn α f T := by
  obtain ⟨C, hC, hb, hh⟩ := hf
  exact ⟨C, hC, fun x hx => hb x (hT hx), fun x hx y hy => hh x (hT hx) y (hT hy)⟩

lemma congr (hf : BoundedHolderOn α f S) (he : EqOn f g S) : BoundedHolderOn α g S := by
  obtain ⟨C, hC, hb, hh⟩ := hf
  refine ⟨C, hC, ?_, ?_⟩
  · intro x hx
    rw [← he hx]
    exact hb x hx
  · intro x hx y hy
    rw [← he hx, ← he hy]
    exact hh x hx y hy

lemma const (c : F) : BoundedHolderOn α (fun _ : E => c) S := by
  refine ⟨‖c‖, norm_nonneg c, fun _ _ => le_rfl, ?_⟩
  intro x hx y hy
  simp only [sub_self, norm_zero]
  positivity

lemma add (hf : BoundedHolderOn α f S) (hg : BoundedHolderOn α g S) :
    BoundedHolderOn α (fun x => f x+g x) S := by
  obtain ⟨C, hC, hfb, hfh⟩ := hf
  obtain ⟨D, hD, hgb, hgh⟩ := hg
  refine ⟨C+D, add_nonneg hC hD, fun x hx => (norm_add_le _ _).trans (add_le_add (hfb x hx) (hgb x hx)), ?_⟩
  intro x hx y hy
  have he : f x+g x-(f y+g y)=(f x-f y)+(g x-g y) := by abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (hfh x hx y hy) (hgh x hx y hy)).trans_eq (by ring))

lemma neg (hf : BoundedHolderOn α f S) : BoundedHolderOn α (fun x => -f x) S := by
  obtain ⟨C, hC, hb, hh⟩ := hf
  refine ⟨C, hC, ?_, ?_⟩
  · intro x hx
    simpa only [norm_neg] using hb x hx
  · intro x hx y hy
    simpa only [neg_sub_neg, norm_sub_rev] using hh x hx y hy

lemma sub (hf : BoundedHolderOn α f S) (hg : BoundedHolderOn α g S) :
    BoundedHolderOn α (fun x => f x-g x) S := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma map [NormedSpace ℝ F] [NormedSpace ℝ G] (hf : BoundedHolderOn α f S) (L : F →L[ℝ] G) :
    BoundedHolderOn α (fun x => L (f x)) S := by
  obtain ⟨C, hC, hb, hh⟩ := hf
  refine ⟨‖L‖*C, by positivity, fun x hx => (L.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg L)), ?_⟩
  intro x hx y hy
  rw [← map_sub]
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hh x hx y hy) (norm_nonneg L)).trans_eq (by ring))

lemma finset_sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, BoundedHolderOn α (f i) S) :
    BoundedHolderOn α (fun x => ∑ i ∈ s, f i x) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (const (E := E) (S := S) (α := α) (0 : F))
  | @insert i s his ih =>
    simpa only [Finset.sum_insert his] using
      (hf i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma pi {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    {f : ∀ i, E → V i} (hf : ∀ i, BoundedHolderOn α (f i) S) :
    BoundedHolderOn α (fun x i => f i x) S := by
  classical
  choose C hC hb hh using hf
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  have hle (i : ι) : C i ≤ ∑ j, C j := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨∑ i, C i, hsum, ?_, ?_⟩
  · intro x hx
    exact (pi_norm_le_iff_of_nonneg hsum).mpr (fun i => (hb i x hx).trans (hle i))
  · intro x hx y hy
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsum (Real.rpow_nonneg (norm_nonneg _) α))).mpr
    intro i
    exact (hh i x hx y hy).trans (mul_le_mul_of_nonneg_right (hle i) (Real.rpow_nonneg (norm_nonneg _) α))

lemma prod {f : E → F} {g : E → G} (hf : BoundedHolderOn α f S) (hg : BoundedHolderOn α g S) :
    BoundedHolderOn α (fun x => (f x, g x)) S := by
  obtain ⟨C, hC, hfb, hfh⟩ := hf
  obtain ⟨D, hD, hgb, hgh⟩ := hg
  refine ⟨max C D, le_max_of_le_left hC, ?_, ?_⟩
  · intro x hx
    rw [Prod.norm_def]
    exact max_le ((hfb x hx).trans (le_max_left _ _)) ((hgb x hx).trans (le_max_right _ _))
  · intro x hx y hy
    rw [Prod.norm_def]
    exact max_le ((hfh x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) α))) ((hgh x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) α)))

lemma clm_apply [NormedSpace ℝ F] [NormedSpace ℝ G]
    {a : E → F →L[ℝ] G} (ha : BoundedHolderOn α a S) (hf : BoundedHolderOn α f S) :
    BoundedHolderOn α (fun x => a x (f x)) S := by
  obtain ⟨A, hA, hab, haH⟩ := ha
  obtain ⟨B, hB, hfb, hfH⟩ := hf
  refine ⟨2*A*B, by positivity, ?_, ?_⟩
  · intro x hx
    apply ((a x).le_opNorm (f x)).trans
    exact (mul_le_mul (hab x hx) (hfb x hx) (norm_nonneg _) hA).trans (by nlinarith)
  · intro x hx y hy
    exact (holder_clm_apply_bound hA hB hA hB hab hfb haH hfH x hx y hy).trans_eq (by ring)

lemma smul [NormedSpace ℝ F] {a : E → ℝ}
    (ha : BoundedHolderOn α a S) (hf : BoundedHolderOn α f S) :
    BoundedHolderOn α (fun x => a x • f x) S := by
  obtain ⟨A, hA, hab, haH⟩ := ha
  obtain ⟨B, hB, hfb, hfH⟩ := hf
  have hab' : ∀ x ∈ S, |a x| ≤ A := by simpa only [Real.norm_eq_abs] using hab
  have haH' : ∀ x ∈ S, ∀ y ∈ S, |a x-a y| ≤ A*‖x-y‖^α := by simpa only [Real.norm_eq_abs] using haH
  refine ⟨2*A*B, by positivity, ?_, ?_⟩
  · intro x hx
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (hab' x hx) (hfb x hx) (norm_nonneg _) hA).trans (by nlinarith)
  · intro x hx y hy
    exact (holder_smul_bound_norm hA hB hA hB hab' hfb haH' hfH x hx y hy).trans_eq (by ring)

lemma mul {f g : E → ℝ} (hf : BoundedHolderOn α f S) (hg : BoundedHolderOn α g S) :
    BoundedHolderOn α (fun x => f x*g x) S := hf.smul hg

lemma multilinear_apply [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {a : E → ContinuousMultilinearMap ℝ V F} {v : E → ∀ i, V i}
    (ha : BoundedHolderOn α a S) (hv : BoundedHolderOn α v S) :
    BoundedHolderOn α (fun x => a x (v x)) S := by
  obtain ⟨A, hA, hab, haH⟩ := ha
  obtain ⟨B, hB, hvb, hvH⟩ := hv
  let D := A*(Fintype.card ι : ℝ)*B^(Fintype.card ι-1)*B+A*B^(Fintype.card ι)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨A*B^(Fintype.card ι)+D, by positivity, ?_, ?_⟩
  · intro x hx
    apply ((a x).le_opNorm (v x)).trans
    apply (mul_le_mul (hab x hx) _ (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hA).trans
      (le_add_of_nonneg_right hD)
    calc
      (∏ i, ‖v x i‖) ≤ ∏ _i : ι, B := Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i _ => (norm_le_pi_norm (v x) i).trans (hvb x hx))
      _ = _ := by simp
  · intro x hx y hy
    have hh := holder_multilinear_apply_bound hA hB hA hB hab hvb haH hvH x hx y hy
    exact hh.trans (mul_le_mul_of_nonneg_right
      (show D ≤ A*B^(Fintype.card ι)+D from le_add_of_nonneg_left (by positivity))
      (Real.rpow_nonneg (norm_nonneg _) α))

end BoundedHolderOn

lemma boundedHolderOn_of_contDiff [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 1 f) {S : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) : BoundedHolderOn α f S := by
  obtain ⟨C, hC, hb, hh⟩ := exists_contDiff_holder_bound_on_compact_convex hf hS hSc hα hα1
  exact ⟨C, hC.le, hb, hh⟩

end GaussianTilt.MomentMapSchauder
