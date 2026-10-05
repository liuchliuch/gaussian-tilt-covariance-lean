import GaussianTilt.PaourisGaussian
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Moments.SubGaussian

/-!
# Analytic inputs for Gaussian Lipschitz concentration

These lemmas concern the normalized, radial Gaussian measure itself.  In
particular the linear exponential moment is computed by completing the square
and translating Lebesgue measure, rather than postulated as a Gaussian axiom.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris
variable {n : ℕ}

lemma gaussianKernel_complete_square (a x : Reference.Space n) :
    Real.exp (⟪a, x⟫_ℝ) * gaussianKernel n x =
      Real.exp (‖a‖ ^ 2 / 2) * gaussianKernel n (x - a) := by
  unfold gaussianKernel
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real, real_inner_comm x a]
  ring

/-- Every linear exponential has an integrable Gaussian density. -/
lemma standardGaussian_exp_inner_integrable (a : Reference.Space n) :
    Integrable (fun x ↦ Real.exp (⟪a, x⟫_ℝ)) (standardGaussian n) := by
  apply (integrable_standardGaussian_iff _).mpr
  simp_rw [gaussianKernel_complete_square]
  exact ((gaussianKernel_integrable n).comp_sub_right a).const_mul _

/-- Exact normalized Gaussian exponential moment. -/
theorem standardGaussian_integral_exp_inner (a : Reference.Space n) :
    (∫ x, Real.exp (⟪a, x⟫_ℝ) ∂standardGaussian n) = Real.exp (‖a‖ ^ 2 / 2) := by
  rw [integral_standardGaussian]
  simp_rw [gaussianKernel_complete_square]
  rw [integral_const_mul, integral_sub_right_eq_self, mul_div_cancel_right₀ _
    (gaussianKernel_integral_pos n).ne']

/-- Exponentials of linear radial growth are genuinely Gaussian integrable. -/
lemma standardGaussian_exp_norm_integrable (c : ℝ) :
    Integrable (fun x : Reference.Space n ↦ Real.exp (c * ‖x‖)) (standardGaussian n) := by
  apply (integrable_standardGaussian_iff _).mpr
  apply ((exp_neg_norm_sq_integrable (n := n)
    (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul (Real.exp (c ^ 2))).mono' (by
      unfold gaussianKernel
      fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  unfold gaussianKernel
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (c - ‖x‖ / 2)]

/-- The moment-generating function of every globally Lipschitz observable is
finite for every real parameter, without boundedness or compact support. -/
lemma standardGaussian_exp_lipschitz_integrable {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * f x)) (standardGaussian n) := by
  apply ((standardGaussian_exp_norm_integrable (n := n) (|t| * K)).const_mul
    (Real.exp (|t| * |f 0|))).mono'
    ((Real.continuous_exp.comp (continuous_const.mul hf.continuous)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := hf.norm_sub_le x 0
  simp only [sub_zero, Real.norm_eq_abs] at hh
  have hh' : |f x| ≤ (K : ℝ) * ‖x‖ + |f 0| := by
    exact (norm_le_norm_sub_add (f x) (f 0)).trans (by
      simpa only [Real.norm_eq_abs] using add_le_add_right hh |f 0|)
  have ht : t * f x ≤ |t| * |f x| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [mul_le_mul_of_nonneg_left hh' (abs_nonneg t)]

/-- Orthogonal invariance follows from the radial density and actual
Lebesgue measure preservation. -/
theorem standardGaussian_integral_isometry
    (A : Reference.Space n ≃ₗᵢ[ℝ] Reference.Space n) (f : Reference.Space n → ℝ) :
    (∫ x, f (A x) ∂standardGaussian n) = ∫ x, f x ∂standardGaussian n := by
  rw [integral_standardGaussian, integral_standardGaussian]
  congr 1
  have h := MeasureTheory.integral_comp A (fun x ↦ f x * gaussianKernel n x)
  simpa only [gaussianKernel, A.norm_map] using h

/-- Exact exponential moment of an arbitrary continuous linear functional. -/
theorem standardGaussian_integral_exp_dual (L : Reference.Space n →L[ℝ] ℝ) :
    (∫ x, Real.exp (L x) ∂standardGaussian n) = Real.exp (‖L‖ ^ 2 / 2) := by
  let a := (InnerProductSpace.toDual ℝ (Reference.Space n)).symm L
  have h := standardGaussian_integral_exp_inner a
  simpa only [a, InnerProductSpace.toDual_symm_apply,
    LinearIsometryEquiv.norm_map] using h

lemma standardGaussian_exp_dual_integrable (L : Reference.Space n →L[ℝ] ℝ) :
    Integrable (fun x ↦ Real.exp (L x)) (standardGaussian n) := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    standardGaussian_exp_inner_integrable
      ((InnerProductSpace.toDual ℝ (Reference.Space n)).symm L)

end GaussianTilt.Paouris
