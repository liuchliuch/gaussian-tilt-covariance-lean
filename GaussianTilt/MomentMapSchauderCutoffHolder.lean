import GaussianTilt.MomentMapSchauderScaledCutoff

/-! # Uniform Hölder bounds for the constructed scaled cutoff jets -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma holder_scale_algebra {r : ℝ} (hr : 0 < r) (α B C : ℝ) (k : ℕ) :
    (B / r ^ (k+1)) * r ^ (1-α) + 2 * (C / r ^ k) * r ^ (-α) =
      (B + 2*C) * r ^ (-(k : ℝ) - α) := by
  have h₁ : (r ^ (k+1))⁻¹ * r ^ (1-α) = r ^ (-(k : ℝ) - α) := by
    rw [← Real.rpow_natCast r (k+1), ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
    congr 1
    push_cast
    ring
  have h₂ : (r ^ k)⁻¹ * r ^ (-α) = r ^ (-(k : ℝ) - α) := by
    rw [← Real.rpow_natCast r k, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
    congr 1
  calc
    _ = B * ((r ^ (k+1))⁻¹ * r ^ (1-α)) + 2*C * ((r ^ k)⁻¹ * r ^ (-α)) := by ring
    _ = _ := by rw [h₁, h₂]; ring

/-- First and second derivative fields of the actual cutoff are globally
Lipschitz with the proved radius powers. -/
theorem exists_scaled_cutoff_jet_holder_bounds {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ B₁ B₂ B₃ : ℝ, 0 < B₁ ∧ 0 < B₂ ∧ 0 < B₃ ∧
      ∀ a : E, ∀ r : ℝ, 0 < r →
      (∀ x, ‖fderiv ℝ (scaledInteriorCutoff a r) x‖ ≤ B₁ / r) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ (scaledInteriorCutoff a r)) x‖ ≤ B₂ / r ^ 2) ∧
      (∀ x y, |scaledInteriorCutoff a r x - scaledInteriorCutoff a r y| ≤
        ((B₁ + 2) * r ^ (-α)) * ‖x-y‖ ^ α) ∧
      (∀ x y, ‖fderiv ℝ (scaledInteriorCutoff a r) x - fderiv ℝ (scaledInteriorCutoff a r) y‖ ≤
        ((B₂ + 2*B₁) * r ^ (-1-α)) * ‖x-y‖ ^ α) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (scaledInteriorCutoff a r)) x -
        fderiv ℝ (fderiv ℝ (scaledInteriorCutoff a r)) y‖ ≤
        ((B₃ + 2*B₂) * r ^ (-2-α)) * ‖x-y‖ ^ α) := by
  obtain ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, hb⟩ := exists_scaled_cutoff_derivative_bounds (E := E)
  refine ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, ?_⟩
  intro a r hr
  let χ := scaledInteriorCutoff a r
  have hχ : ContDiff ℝ 3 χ := contDiff_infty.mp (scaledInteriorCutoff_contDiff a r) 3
  have hDχ := (hχ.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have hD2χ := ((hχ.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiable le_rfl
  have hLip₀ : ∀ x y : E, ‖χ x - χ y‖ ≤ (B₁ / r) * ‖x-y‖ := by
    intro x y
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hχ.differentiable (by norm_num) z) (fun z _ => (hb a r hr z).1)
      convex_univ (mem_univ y) (mem_univ x)
  have hLip₁ : ∀ x y : E, ‖fderiv ℝ χ x - fderiv ℝ χ y‖ ≤ (B₂ / r^2) * ‖x-y‖ := by
    intro x y
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hDχ z) (fun z _ => (hb a r hr z).2.1)
      convex_univ (mem_univ y) (mem_univ x)
  have hLip₂ : ∀ x y : E, ‖fderiv ℝ (fderiv ℝ χ) x - fderiv ℝ (fderiv ℝ χ) y‖ ≤
      (B₃ / r^3) * ‖x-y‖ := by
    intro x y
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hD2χ z) (fun z _ => (hb a r hr z).2.2)
      convex_univ (mem_univ y) (mem_univ x)
  refine ⟨fun x => (hb a r hr x).1, fun x => (hb a r hr x).2.1, ?_, ?_, ?_⟩
  · have hh := holder_bound_of_sup_and_lipschitz (f := χ) (S := Set.univ)
      (U := 1) (L := B₁/r) (α := α) (ρ := r) zero_le_one (by positivity) hα hα1 hr
      (fun x _ => by rw [Real.norm_eq_abs, abs_of_nonneg (scaledInteriorCutoff_nonneg a x r)]; exact scaledInteriorCutoff_le_one a x r)
      (fun x _ y _ => hLip₀ x y)
    intro x y
    have hx := hh x (mem_univ x) y (mem_univ y)
    have he := holder_scale_algebra hr α B₁ 1 0
    norm_num only [Nat.cast_zero, zero_add, neg_zero, zero_sub, pow_one, pow_zero, div_one, mul_one] at he
    simp only [mul_one] at hx
    rw [he] at hx
    simpa only [Real.norm_eq_abs] using hx
  · have hh := holder_bound_of_sup_and_lipschitz (f := fderiv ℝ χ) (S := Set.univ)
      (U := B₁/r) (L := B₂/r^2) (α := α) (ρ := r) (by positivity) (by positivity) hα hα1 hr
      (fun x _ => (hb a r hr x).1) (fun x _ y _ => hLip₁ x y)
    intro x y
    have hx := hh x (mem_univ x) y (mem_univ y)
    have he := holder_scale_algebra hr α B₂ B₁ 1
    norm_num only [Nat.cast_one, Nat.reduceAdd, pow_one] at he
    rw [he] at hx
    exact hx
  · have hh := holder_bound_of_sup_and_lipschitz (f := fderiv ℝ (fderiv ℝ χ)) (S := Set.univ)
      (U := B₂/r^2) (L := B₃/r^3) (α := α) (ρ := r) (by positivity) (by positivity) hα hα1 hr
      (fun x _ => (hb a r hr x).2.1) (fun x _ y _ => hLip₂ x y)
    intro x y
    have hx := hh x (mem_univ x) y (mem_univ y)
    have he := holder_scale_algebra hr α B₃ B₂ 2
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at he
    rw [he] at hx
    exact hx

end GaussianTilt.MomentMapSchauder
