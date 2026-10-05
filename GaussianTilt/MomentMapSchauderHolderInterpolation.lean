import GaussianTilt.MomentMapSchauderHessianInterpolation
import GaussianTilt.MomentMapSchauderCutoff

/-!
# Elementary Hölder interpolation and localization estimates

Supremum and Lipschitz bounds give quantitative Hölder bounds at an arbitrary
positive scale. This permits lower derivative cutoff errors to be absorbed
using the actual Hessian interpolation estimate.
-/
noncomputable section
open Set InnerProductSpace
open scoped ContDiff BigOperators Gradient
namespace GaussianTilt.MomentMapSchauder

/-- Hölder interpolation at an arbitrary positive scale, with no hidden
seminorm finiteness premise. -/
theorem holder_bound_of_sup_and_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : E → F} {S : Set E}
    {U L α ρ : ℝ} (hU : 0 ≤ U) (hL : 0 ≤ L) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hρ : 0 < ρ)
    (hbound : ∀ x ∈ S, ‖f x‖ ≤ U)
    (hlip : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤
      (L * ρ ^ (1 - α) + 2 * U * ρ ^ (-α)) * ‖x - y‖ ^ α := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    positivity
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hp : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg hd.le _
  have hρp : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ _
  by_cases hsmall : ‖x - y‖ ≤ ρ
  · have hpow : ‖x - y‖ ^ (1 - α) ≤ ρ ^ (1 - α) :=
      Real.rpow_le_rpow hd.le hsmall (sub_nonneg.mpr hα1)
    have he : ‖x - y‖ = ‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α := by
      rw [← Real.rpow_add hd]
      convert (Real.rpow_one ‖x - y‖).symm using 1 <;> congr 1 <;> ring
    calc
      _ ≤ L * ‖x - y‖ := hlip x hx y hy
      _ = L * (‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α) := congrArg (fun t => L * t) he
      _ ≤ L * (ρ ^ (1 - α) * ‖x - y‖ ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hp) hL
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * U)
        (Real.rpow_nonneg hρ.le (-α))) hp]
  · have hpow : ρ ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow hρ.le (le_of_not_ge hsmall) hα
    have hone : 1 ≤ ρ ^ (-α) * ‖x - y‖ ^ α := by
      rw [Real.rpow_neg hρ.le, ← div_eq_inv_mul]
      exact (one_le_div hρp).mpr hpow
    have hnorm : ‖f x - f y‖ ≤ 2 * U :=
      (norm_sub_le _ _).trans (by linarith [hbound x hx, hbound y hy])
    have hb := mul_le_mul_of_nonneg_left hone (by positivity : 0 ≤ 2 * U)
    have ht : 0 ≤ L * ρ ^ (1 - α) * ‖x - y‖ ^ α := by positivity
    nlinarith

/-- A cutoff product is globally Hölder from data only on the open region
containing its support; no extension of the original function is assumed. -/
theorem global_holder_cutoff_product {E : Type*} [NormedAddCommGroup E]
    {χ f : E → ℝ} {S : Set E} {A U Cχ Cf α : ℝ}
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hCχ : 0 ≤ Cχ) (hCf : 0 ≤ Cf)
    (hχbound : ∀ x, |χ x| ≤ A) (hfbound : ∀ x ∈ S, |f x| ≤ U)
    (hχ : ∀ x y, |χ x - χ y| ≤ Cχ * ‖x - y‖ ^ α)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ Cf * ‖x - y‖ ^ α)
    (hsupp : ∀ x ∉ S, χ x = 0) :
    ∀ x y, |χ x * f x - χ y * f y| ≤ (A * Cf + U * Cχ) * ‖x - y‖ ^ α := by
  intro x y
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · exact holder_product_bound hA hU hCχ hCf (fun z _ => hχbound z) hfbound
        (fun z _ w _ => hχ z w) hf x hx y hy
    · have hχy := hsupp y hy
      rw [hχy, zero_mul, sub_zero, abs_mul]
      have hc : |χ x| ≤ Cχ * ‖x - y‖ ^ α := by simpa only [hχy, sub_zero] using hχ x y
      have hb := mul_le_mul hc (hfbound x hx) (abs_nonneg _) (by positivity)
      exact hb.trans (by nlinarith [mul_nonneg (mul_nonneg hA hCf) (Real.rpow_nonneg (norm_nonneg (x-y)) α)])
  · have hχx := hsupp x hx
    by_cases hy : y ∈ S
    · rw [hχx, zero_mul, zero_sub, abs_neg, abs_mul]
      have hc : |χ y| ≤ Cχ * ‖x - y‖ ^ α := by
        simpa only [hχx, sub_zero, norm_sub_rev] using hχ y x
      have hb := mul_le_mul hc (hfbound y hy) (abs_nonneg _) (by positivity)
      exact hb.trans (by nlinarith [mul_nonneg (mul_nonneg hA hCf) (Real.rpow_nonneg (norm_nonneg (x-y)) α)])
    · simp only [hχx, hsupp y hy, zero_mul, sub_self, abs_zero]
      positivity

/-- Uniform bound on the actual Taylor quadratic jet from function size and
an actual Hölder second derivative on the containing ball. -/
theorem taylorQuadraticJet_uniform_bound {n : ℕ}
    {u : GaussianTilt.MomentMapRegularity.E n → ℝ} (hu : ContDiff ℝ 2 u)
    {x : GaussianTilt.MomentMapRegularity.E n} {r U C α : ℝ}
    (hr : 0 < r) (hU : 0 ≤ U) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hub : ∀ y ∈ Metric.closedBall x r, |u y| ≤ U)
    (hH : ∀ y ∈ Metric.closedBall x r, ∀ z ∈ Metric.closedBall x r,
      ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ ≤ C * ‖y - z‖ ^ α) :
    ∀ v : GaussianTilt.MomentMapRegularity.E n, ‖v‖ ≤ r →
      |GaussianTilt.MomentMapRegularity.quadraticJet (u x) (gradient u x) 0 (frechetHessian u x) v| ≤
        U + (C / 2) * r ^ α * r ^ 2 := by
  intro v hv
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ Metric.closedBall x r := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hv
  have ht := taylor_second_remainder_holder_on hu hC hα hH
    (by simpa using hr.le : x ∈ Metric.closedBall x r) hseg
  have he : u (x + v) - GaussianTilt.MomentMapRegularity.quadraticJet (u x) (gradient u x) 0 (frechetHessian u x) v =
      u (x + v) - u x - fderiv ℝ u x v - (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ u) x v v := by
    simp only [GaussianTilt.MomentMapRegularity.quadraticJet, sub_zero,
      inner_gradient_eq_fderiv, inner_frechetHessian]
    ring
  rw [← he] at ht
  have hp := Real.rpow_le_rpow (norm_nonneg v) hv hα
  have hv2 := (sq_le_sq₀ (norm_nonneg v) hr.le).mpr hv
  have herr := ht.trans (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hv2
    (sq_nonneg _) (by positivity))
  have hubv := hub (x + v) (by simpa using hseg 1 ⟨by norm_num, le_rfl⟩)
  calc
    _ = |u (x + v) - (u (x + v) - GaussianTilt.MomentMapRegularity.quadraticJet
        (u x) (gradient u x) 0 (frechetHessian u x) v)| := by congr 1; ring
    _ ≤ |u (x + v)| + |u (x + v) - GaussianTilt.MomentMapRegularity.quadraticJet
        (u x) (gradient u x) 0 (frechetHessian u x) v| := abs_sub _ _
    _ ≤ _ := add_le_add hubv herr

/-- The gradient interpolation companion to the actual Hessian estimate. -/
theorem gradient_interpolation_on_closedBall {n : ℕ}
    {u : GaussianTilt.MomentMapRegularity.E n → ℝ} (hu : ContDiff ℝ 2 u)
    {x : GaussianTilt.MomentMapRegularity.E n} {r U C α : ℝ}
    (hr : 0 < r) (hU : 0 ≤ U) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hub : ∀ y ∈ Metric.closedBall x r, |u y| ≤ U)
    (hH : ∀ y ∈ Metric.closedBall x r, ∀ z ∈ Metric.closedBall x r,
      ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ ≤ C * ‖y - z‖ ^ α) :
    ‖fderiv ℝ u x‖ ≤ U / r + (C / 2) * r ^ α * r := by
  have hb := GaussianTilt.MomentMapRegularity.quadraticJet_gradient_norm_bound
    (u x) (gradient u x) (frechetHessian u x) hr (by positivity)
    (taylorQuadraticJet_uniform_bound hu hr hU hC hα hub hH)
  have hn : ‖gradient u x‖ = ‖fderiv ℝ u x‖ :=
    (InnerProductSpace.toDual ℝ (GaussianTilt.MomentMapRegularity.E n)).symm.norm_map _
  rw [hn] at hb
  exact hb.trans_eq (by field_simp)

end GaussianTilt.MomentMapSchauder
