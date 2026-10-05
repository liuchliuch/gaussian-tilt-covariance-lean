import GaussianTilt.MomentMapSchauderInterpolation

/-!
# Difference-quotient bounds uniform in the step

The integral formula is derived by FTC. Supremum and Hölder bounds come
from the actual first derivative and contain no inverse-step loss.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma continuous_line_fderiv_apply {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    (x h e : E) : Continuous (fun t : ℝ => fderiv ℝ u (x + t • h) e) := by
  have hd : Continuous (fderiv ℝ u) := (hu.fderiv_right (m := 0) (by norm_num)).continuous
  exact (hd.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

/-- FTC representation of the actual difference quotient. -/
theorem differenceQuotient_eq_integral_fderiv {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    (x e : E) {s : ℝ} (hs : s ≠ 0) :
    s⁻¹ * (u (x + s • e) - u x) =
      ∫ t in (0 : ℝ)..1, fderiv ℝ u (x + t • (s • e)) e := by
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ => u (x + r • (s • e)))
      (s * fderiv ℝ u (x + t • (s • e)) e) t := by
    simpa only [Function.comp_def, id_eq, one_smul, map_smul, smul_eq_mul] using
      ((hu.differentiable le_rfl (x + t • (s • e))).hasFDerivAt.comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const (s • e)).const_add x))
  have hint : IntervalIntegrable
      (fun t => s * fderiv ℝ u (x + t • (s • e)) e) volume 0 1 :=
    (continuous_const.mul (continuous_line_fderiv_apply hu x (s • e) e)).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hint
  simp only [zero_smul, one_smul, add_zero, intervalIntegral.integral_const_mul] at he
  rw [← he]
  rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- Uniform supremum bound for finite differences from a first-derivative
bound on the actual interpolation segment. -/
theorem abs_differenceQuotient_le {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    (x e : E) {s M : ℝ} (hs : s ≠ 0)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • (s • e))‖ ≤ M) :
    |s⁻¹ * (u (x + s • e) - u x)| ≤ M * ‖e‖ := by
  rw [differenceQuotient_eq_integral_fderiv hu x e hs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M * ‖e‖)
    (f := fun t => fderiv ℝ u (x + t • (s • e)) e) ?_
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)
    exact ((fderiv ℝ u (x + t • (s • e))).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right (hM t ht') (norm_nonneg e))

/-- A Hölder first derivative gives the same Hölder exponent for difference
quotients, uniformly over nonzero scalar steps. -/
theorem differenceQuotient_holder_bound {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    {S : Set E} {C α : ℝ}
    (hH : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ C * ‖x - y‖ ^ α)
    (x y e : E) {s : ℝ} (hs : s ≠ 0)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (s • e) ∈ S)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (s • e) ∈ S) :
    |s⁻¹ * (u (x + s • e) - u x) - s⁻¹ * (u (y + s • e) - u y)| ≤
      (C * ‖e‖) * ‖x - y‖ ^ α := by
  rw [differenceQuotient_eq_integral_fderiv hu x e hs,
    differenceQuotient_eq_integral_fderiv hu y e hs,
    ← intervalIntegral.integral_sub
      (continuous_line_fderiv_apply hu x (s • e) e |>.intervalIntegrable 0 1)
      (continuous_line_fderiv_apply hu y (s • e) e |>.intervalIntegrable 0 1)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (C * ‖e‖) * ‖x - y‖ ^ α)
    (f := fun t => fderiv ℝ u (x + t • (s • e)) e - fderiv ℝ u (y + t • (s • e)) e) ?_
  · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)
    have he : (x + t • (s • e)) - (y + t • (s • e)) = x - y := by abel
    have hholder := hH _ (hx t ht') _ (hy t ht')
    rw [he] at hholder
    have hn := (fderiv ℝ u (x + t • (s • e)) - fderiv ℝ u (y + t • (s • e))).le_opNorm e
    have hmul := mul_le_mul_of_nonneg_right hholder (norm_nonneg e)
    simpa only [ContinuousLinearMap.sub_apply, mul_assoc, mul_left_comm, mul_comm] using hn.trans hmul

end GaussianTilt.MomentMapSchauder
