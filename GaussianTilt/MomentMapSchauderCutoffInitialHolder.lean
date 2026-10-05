import GaussianTilt.MomentMapSchauderCutoffForcing

/-! # Preservation of finite second-derivative Hölder bounds under cutoff -/
noncomputable section
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Local finite C²,α data produce an actual global finite Hessian Hölder
bound after multiplication by a compactly supported cutoff. The initial
constant may depend on a difference-quotient step, since the Schauder
absorption theorem removes it. -/
theorem localized_secondFrechet_holder {χ u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ) {S : Set (KernelSpace n)}
    {C₀ C₁ C₂ L₀ L₁ L₂ U D J HU HD HJ α : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hU : 0 ≤ U) (hD : 0 ≤ D) (hJ : 0 ≤ J)
    (hHU : 0 ≤ HU) (hHD : 0 ≤ HD) (hHJ : 0 ≤ HJ)
    (hs : tsupport χ ⊆ S)
    (hχ₀ : ∀ x, |χ x| ≤ C₀)
    (hχ₁ : ∀ x, ‖fderiv ℝ χ x‖ ≤ C₁)
    (hχ₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ C₂)
    (hχH₀ : ∀ x y, |χ x-χ y| ≤ L₀*‖x-y‖^α)
    (hχH₁ : ∀ x y, ‖fderiv ℝ χ x-fderiv ℝ χ y‖ ≤ L₁*‖x-y‖^α)
    (hχH₂ : ∀ x y, ‖fderiv ℝ (fderiv ℝ χ) x-fderiv ℝ (fderiv ℝ χ) y‖ ≤ L₂*‖x-y‖^α)
    (hub : ∀ x ∈ S, |u x| ≤ U) (hDu : ∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ D)
    (hD2u : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ J)
    (huH : ∀ x ∈ S, ∀ y ∈ S, |u x-u y| ≤ HU*‖x-y‖^α)
    (hDuH : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ HD*‖x-y‖^α)
    (hD2uH : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ HJ*‖x-y‖^α) :
    ∀ x y, ‖fderiv ℝ (fderiv ℝ (fun z => χ z*u z)) x-
      fderiv ℝ (fderiv ℝ (fun z => χ z*u z)) y‖ ≤
      ((n : ℝ)^2*(C₀*HJ+J*L₀+C₂*HU+U*L₂+2*(C₁*HD+D*L₁)))*‖x-y‖^α := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hP (i j : Fin n) := global_holder_cutoff_product hC₀ hJ hL₀ hHJ hχ₀
    (f := fun x => fderiv ℝ (fderiv ℝ u) x (e i) (e j))
    (fun x hx => (abs_euclidean_bilinear_entry_le_norm _ i j).trans (hD2u x hx)) hχH₀
    (fun x hx y hy => (abs_euclidean_bilinear_entry_le_norm
      (fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y) i j).trans (hD2uH x hx y hy))
    (fun x hx => (cutoff_jets_zero_off hs hx).1)
  have hQ (i j : Fin n) := global_holder_cutoff_product hC₂ hU hL₂ hHU
    (χ := fun x => fderiv ℝ (fderiv ℝ χ) x (e i) (e j))
    (fun x => (abs_euclidean_bilinear_entry_le_norm _ i j).trans (hχ₂ x)) hub
    (fun x y => (abs_euclidean_bilinear_entry_le_norm
      (fderiv ℝ (fderiv ℝ χ) x-fderiv ℝ (fderiv ℝ χ) y) i j).trans (hχH₂ x y)) huH
    (fun x hx => by dsimp only; rw [(cutoff_jets_zero_off hs hx).2.2]; simp)
  have hR (i j : Fin n) := global_holder_cutoff_product hC₁ hD hL₁ hHD
    (χ := fun x => fderiv ℝ χ x (e i)) (f := fun x => fderiv ℝ u x (e j))
    (fun x => (abs_euclidean_linear_entry_le_norm _ i).trans (hχ₁ x))
    (fun x hx => (abs_euclidean_linear_entry_le_norm _ j).trans (hDu x hx))
    (fun x y => (abs_euclidean_linear_entry_le_norm
      (fderiv ℝ χ x-fderiv ℝ χ y) i).trans (hχH₁ x y))
    (fun x hx y hy => (abs_euclidean_linear_entry_le_norm
      (fderiv ℝ u x-fderiv ℝ u y) j).trans (hDuH x hx y hy))
    (fun x hx => by dsimp only; rw [(cutoff_jets_zero_off hs hx).2.1]; simp)
  intro x y
  apply (euclidean_bilinear_norm_le_of_entries _ (M :=
    (C₀*HJ+J*L₀+C₂*HU+U*L₂+2*(C₁*HD+D*L₁))*‖x-y‖^α) (by positivity) ?_).trans_eq (by ring)
  intro i j
  simp only [ContinuousLinearMap.sub_apply, secondFrechet_mul_apply hu hχ]
  have hh := holder_sum_two (holder_sum_two (holder_sum_two (hP i j) (hQ i j)) (hR i j)) (hR j i) x y
  convert hh using 1 <;> dsimp [e] <;> congr 1 <;> ring

end GaussianTilt.MomentMapSchauder
