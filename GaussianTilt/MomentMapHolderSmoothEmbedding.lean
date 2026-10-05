import GaussianTilt.MomentMapHolderJetCompactness

/-! # Actual smooth functions embed into the constructed Hölder jet domain -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction ContDiff
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma holder_bound_of_bounded_lipschitz (X : Type*) [MetricSpace X]
    (f : X →ᵇ F) {α L : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * dist x y) :
    ∀ x y, ‖f x - f y‖ ≤ max L (2 * ‖f‖) * dist x y ^ α := by
  intro x y
  by_cases hd : dist x y ≤ 1
  · exact (hf x y).trans ((mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_le_one dist_nonneg hd hα1) hL).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)))
  · have hn : ‖f x - f y‖ ≤ 2 * ‖f‖ := by
      exact (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm y])
    exact hn.trans ((le_mul_of_one_le_right (by positivity : 0 ≤ 2 * ‖f‖)
      (Real.one_le_rpow (le_of_lt (lt_of_not_ge hd)) hα)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)))

/-- Smoothness and compact convex geometry derive the finite actual Hölder
norm, rather than supplying membership as a separate function-space premise. -/
theorem exists_holder_restriction_of_smooth {S : Set E} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ∃ g : Space S F α, ∀ x : S, value S F α g x = f x := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let b : S →ᵇ F := BoundedContinuousFunction.mkOfCompact ⟨fun x : S => f x,
    hf.continuous.comp continuous_subtype_val⟩
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn
    (hf.continuous_fderiv (by simp)).continuousOn
  let L := max B 0
  have hL : 0 ≤ L := le_max_right _ _
  have hLip : ∀ x y : S, ‖b x - b y‖ ≤ L * dist x y := by
    intro x y
    change ‖f x - f y‖ ≤ L * dist (x : E) y
    rw [dist_eq_norm]
    exact hS.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hf.differentiable (by simp) x)
      (fun x hx => (hB x hx).trans (le_max_left B 0)) y.2 x.2
  refine ⟨ofBounded S F α b (max L (2 * ‖b‖))
    (holder_bound_of_bounded_lipschitz S b hα hα1 hL hLip), fun _ => rfl⟩

/-- The literal segment FTC identity for a smooth function and its actual
Fréchet derivative, on the true convex-domain segment. -/
lemma smooth_segment_ftc {S : Set E} (hS : Convex ℝ S) (f : E → F)
    (hf : ContDiff ℝ ∞ f) (x y : S) :
    f y - f x = ∫ t in (0 : ℝ)..1,
      fderiv ℝ f (segmentPoint hS x y t) ((y : E) - x) := by
  let path : ℝ → E := fun t => (x : E) + t • ((y : E) - x)
  have hp (t : ℝ) : HasDerivAt path ((y : E) - x) t := by
    simpa only [path, one_smul] using ((hasDerivAt_id t).smul_const ((y : E) - x)).const_add (x : E)
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => f (path t))
      (fderiv ℝ f (path t) ((y : E) - x)) t := by
    intro t _
    exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hi : IntervalIntegrable (fun t => fderiv ℝ f (path t) ((y : E) - x)) volume 0 1 :=
    (((hf.continuous_fderiv (by simp)).comp (by unfold path; fun_prop)).clm_apply continuous_const).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simp only [path, zero_smul, add_zero, one_smul, add_sub_cancel] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [segmentPoint_eq hS x y (by simpa only [uIcc_of_le zero_le_one] using ht)]

/-- Every actual smooth function has its true value/first/second fields in
the complete C²,α jet space; both FTC constraints are derived. -/
theorem exists_jet_of_smooth {S : Set E} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ∃ j : Jet E F hS α,
      (∀ x : S, value S F α (jetValue E F hS α j) x = f x) ∧
      (∀ x : S, value S (E →L[ℝ] F) α (jetFirst E F hS α j) x = fderiv ℝ f x) ∧
      (∀ x : S, value S (E →L[ℝ] E →L[ℝ] F) α (jetSecond E F hS α j) x = fderiv ℝ (fderiv ℝ f) x) := by
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hHf : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hDf.fderiv_right (by simp)
  obtain ⟨u, hu⟩ := exists_holder_restriction_of_smooth hS hSc hα hα1 f hf
  obtain ⟨D, hD⟩ := exists_holder_restriction_of_smooth hS hSc hα hα1 (fderiv ℝ f) hDf
  obtain ⟨H, hH⟩ := exists_holder_restriction_of_smooth hS hSc hα hα1 (fderiv ℝ (fderiv ℝ f)) hHf
  have h₀ : ∀ x y, value S F α u y - value S F α u x = segmentIntegral hS α x y D := by
    intro x y
    rw [hu, hu, segmentIntegral_apply]
    simp_rw [hD]
    exact smooth_segment_ftc hS f hf x y
  have h₁ : ∀ x y, value S (E →L[ℝ] F) α D y - value S (E →L[ℝ] F) α D x = segmentIntegral hS α x y H := by
    intro x y
    rw [hD, hD, segmentIntegral_apply]
    simp_rw [hH]
    exact smooth_segment_ftc hS (fderiv ℝ f) hDf x y
  exact ⟨ofFields hS α u D H h₀ h₁, hu, hD, hH⟩

end GaussianTilt.HolderSpace
