import GaussianTilt.SmoothComparison
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Gaussian-smoothed replacement estimates

The Gaussian smoothing variance is retained as a parameter so that successive
Lindeberg replacements can use the additional smoothing from already replaced
summands. This is the quantitative distributional step needed for the general
Cramér–Petrov range.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.GaussianSmoothing
open SmoothComparison

lemma gaussian_cdf_eq_integral {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    cdf (gaussianReal 0 v) x = ∫ y in Set.Iic x, gaussianPDFReal 0 v y := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ hv,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))]

lemma gaussianPDF_contDiff (v : ℝ≥0) (n : ℕ) : ContDiff ℝ n (gaussianPDFReal 0 v) := by
  unfold gaussianPDFReal
  fun_prop

lemma gaussian_cdf_hasDerivAt {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (cdf (gaussianReal 0 v)) (gaussianPDFReal 0 v x) x := by
  have heq : (cdf (gaussianReal 0 v) : ℝ → ℝ) =
      fun y ↦ cdf (gaussianReal 0 v) 0 + ∫ z in (0 : ℝ)..y, gaussianPDFReal 0 v z := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic
      (integrable_gaussianPDFReal 0 v).integrableOn
      (integrable_gaussianPDFReal 0 v).integrableOn (a := (0 : ℝ)) (b := y)
    rw [← gaussian_cdf_eq_integral hv y, ← gaussian_cdf_eq_integral hv 0] at h
    linarith
  rw [heq]
  convert (intervalIntegral.integral_hasDerivAt_right
    ((gaussianPDF_contDiff v 1).continuous.intervalIntegrable 0 x)
    (gaussianPDF_contDiff v 1).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (gaussianPDF_contDiff v 1).continuous.continuousAt).const_add (cdf (gaussianReal 0 v) 0) using 1

lemma gaussian_cdf_deriv {v : ℝ≥0} (hv : v ≠ 0) :
    deriv (cdf (gaussianReal 0 v)) = gaussianPDFReal 0 v := by
  funext x
  exact (gaussian_cdf_hasDerivAt hv x).deriv

lemma gaussian_cdf_contDiff {v : ℝ≥0} (hv : v ≠ 0) (n : ℕ) :
    ContDiff ℝ n (cdf (gaussianReal 0 v)) := by
  cases n with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun x ↦ (gaussian_cdf_hasDerivAt hv x).continuousAt))
  | succ n =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_deriv]
    refine ⟨fun x ↦ (gaussian_cdf_hasDerivAt hv x).differentiableAt, ?_, ?_⟩
    · intro h
      simp at h
    · rw [gaussian_cdf_deriv hv]
      exact gaussianPDF_contDiff v n

lemma gaussianPDF_hasDerivAt {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-x / (v : ℝ) * gaussianPDFReal 0 v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hq : HasDerivAt (fun y : ℝ ↦ -y ^ 2 / (2 * (v : ℝ))) (-x / (v : ℝ)) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const (2 * (v : ℝ)) using 1
    dsimp
    field_simp
  convert hq.exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹ using 1
  · ext y
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal, sub_zero]
    ring

lemma gaussianPDF_second_hasDerivAt {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun y ↦ -y / (v : ℝ) * gaussianPDFReal 0 v y)
      ((x ^ 2 / (v : ℝ) ^ 2 - 1 / (v : ℝ)) * gaussianPDFReal 0 v x) x := by
  convert ((hasDerivAt_id x).neg.div_const (v : ℝ)).mul (gaussianPDF_hasDerivAt hv x) using 1
  dsimp
  ring

lemma gaussian_cdf_third {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    iteratedDeriv 3 (cdf (gaussianReal 0 v)) x =
      (x ^ 2 / (v : ℝ) ^ 2 - 1 / (v : ℝ)) * gaussianPDFReal 0 v x := by
  have hpdf : deriv (gaussianPDFReal 0 v) = fun y ↦ -y / (v : ℝ) * gaussianPDFReal 0 v y := by
    funext y
    exact (gaussianPDF_hasDerivAt hv y).deriv
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
    show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
    gaussian_cdf_deriv hv, hpdf]
  exact (gaussianPDF_second_hasDerivAt hv x).deriv

lemma gaussian_cdf_third_bound {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    |iteratedDeriv 3 (cdf (gaussianReal 0 v)) x| ≤
      3 / ((v : ℝ) * Real.sqrt (2 * Real.pi * v)) := by
  have hvp : 0 < (v : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  let y : ℝ := x ^ 2 / (2 * (v : ℝ))
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hex : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hye : y * Real.exp (-y) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp y) (Real.exp_nonneg (-y))
    have he : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    rw [he] at h
    nlinarith [Real.exp_nonneg (-y)]
  have hxe : x ^ 2 * Real.exp (-y) ≤ 2 * (v : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hye (show 0 ≤ 2 * (v : ℝ) by positivity)
    dsimp [y] at hh
    field_simp at hh
    nlinarith only [hh]
  have hcoef : |x ^ 2 / (v : ℝ) ^ 2 - 1 / (v : ℝ)| ≤
      x ^ 2 / (v : ℝ) ^ 2 + 1 / (v : ℝ) := by
    apply abs_le.mpr
    have h1 : 0 ≤ x ^ 2 / (v : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ 1 / (v : ℝ) := by positivity
    constructor <;> linarith
  have hsum : (x ^ 2 / (v : ℝ) ^ 2 + 1 / (v : ℝ)) * Real.exp (-y) ≤ 3 / (v : ℝ) := by
    apply (le_div_iff₀ hvp).mpr
    have hh := mul_le_mul_of_nonneg_left hex hvp.le
    have hn : (x ^ 2 / (v : ℝ) ^ 2 + 1 / (v : ℝ)) * Real.exp (-y) * (v : ℝ) =
        (x ^ 2 * Real.exp (-y) + (v : ℝ) * Real.exp (-y)) / (v : ℝ) := by field_simp
    rw [hn]
    apply (div_le_iff₀ hvp).mpr
    nlinarith only [hxe, hh]
  rw [gaussian_cdf_third hv, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  unfold gaussianPDFReal
  simp only [sub_zero, neg_div]
  change _ * ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-y)) ≤ _
  calc
    _ ≤ (x ^ 2 / (v : ℝ) ^ 2 + 1 / (v : ℝ)) *
        ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-y)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ *
        ((x ^ 2 / (v : ℝ) ^ 2 + 1 / (v : ℝ)) * Real.exp (-y)) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * (3 / (v : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The Gaussian convolution formula, directly at the level of actual CDFs. -/
lemma cdf_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a : ℝ) :
    cdf (μ ∗ ν) a = ∫ x, cdf ν (a - x) ∂μ := by
  let f : ℝ → ℝ := (Set.Iic a).indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator measurableSet_Iic
  have hB : ∀ x, |f x| ≤ 1 := by
    intro x
    by_cases hx : x ≤ a <;> simp [f, hx]
  have he (ρ : Measure ℝ) [IsProbabilityMeasure ρ] : cdf ρ a = ∫ x, f x ∂ρ := by
    rw [cdf_eq_real, integral_indicator_const 1 measurableSet_Iic]
    simp only [smul_eq_mul, mul_one]
  rw [he, show (∫ x, f x ∂(μ ∗ ν)) = ∫ x, f (0 + x) ∂(μ ∗ ν) by simp,
    integral_conv_bounded hf hB 0]
  apply integral_congr_ae
  filter_upwards [] with x
  have hinner : (fun y ↦ f (0 + (x + y))) =
      (Set.Iic (a - x)).indicator (fun _ ↦ (1 : ℝ)) := by
    ext y
    by_cases hy : y ≤ a - x
    · have hxy : x + y ≤ a := by linarith
      simp [f, hxy, hy]
    · have hxy : ¬ x + y ≤ a := by linarith
      simp [f, hxy, hy]
  rw [hinner, integral_indicator_const 1 measurableSet_Iic, cdf_eq_real]
  simp

lemma cdf_convolution_comparison {μ ν ρ : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {E : ℝ} (hE : ∀ a, |cdf μ a - cdf ν a| ≤ E) (a : ℝ) :
    |cdf (ρ ∗ μ) a - cdf (ρ ∗ ν) a| ≤ E := by
  have hi (η : Measure ℝ) [IsProbabilityMeasure η] :
      Integrable (fun x ↦ cdf η (a - x)) ρ := by
    apply Integrable.of_bound
      (((monotone_cdf η).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) 1
    filter_upwards [] with x
    simp only [Function.comp_apply, id_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg _ _)]
    exact cdf_le_one _ _
  rw [cdf_conv, cdf_conv, ← integral_sub (hi μ) (hi ν), ← Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ := ρ)
    (f := fun x ↦ cdf μ (a - x) - cdf ν (a - x)) (C := E)
    (ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs] using hE (a - x)))
  simpa only [measureReal_univ_eq_one, mul_one] using hh

/-- One replacement, retaining the Gaussian smoothing variance rather than
bounding every step at the smallest smoothing scale. -/
theorem gaussian_smoothed_replacement {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hsecond : ∫ x, x ^ 2 ∂μ = 1)
    {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    |cdf (μ ∗ gaussianReal 0 v) a - cdf (gaussianReal 0 (v + 1)) a| ≤
      (3 / ((v : ℝ) * Real.sqrt (2 * Real.pi * v))) / 6 *
        (thirdMoment μ + thirdMoment (gaussianReal 0 1)) := by
  let f : ℝ → ℝ := fun x ↦ cdf (gaussianReal 0 v) (-x)
  have hf : ContDiff ℝ 3 f := (gaussian_cdf_contDiff hv 3).comp contDiff_neg
  have hB : ∀ x, |f x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (cdf_nonneg _ _)]
    exact cdf_le_one _ _
  have hC : ∀ x, |iteratedDeriv 3 f x| ≤ 3 / ((v : ℝ) * Real.sqrt (2 * Real.pi * v)) := by
    intro x
    rw [show f = fun y ↦ cdf (gaussianReal 0 v) (-y) from rfl, iteratedDeriv_comp_neg]
    simpa only [show (-1 : ℝ) ^ 3 = -1 by norm_num, neg_one_smul, abs_neg] using
      gaussian_cdf_third_bound hv (-x)
  have hν1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hν2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have h := one_step_replacement hf hB hC hμ1 hν1 hμ2 hν2 hμ3
    (gaussian_third_moment_integrable 1) (hmean.trans integral_id_gaussianReal.symm)
    (hsecond.trans (gaussian_second_moment 1).symm) (-a)
  have heq (x : ℝ) : f (-a + x) = cdf (gaussianReal 0 v) (a - x) := by
    dsimp [f]
    congr 1
    ring
  simp_rw [heq] at h
  rw [← cdf_conv, ← cdf_conv, gaussianReal_conv_gaussianReal] at h
  simpa only [zero_add, add_comm 1 v] using h

/-- The finite replacement error with its increasing Gaussian smoothing
variance. The decreasing summands are the improvement over the fixed-test
Lindeberg estimate. -/
def smoothingError (μ : Measure ℝ) (n : ℕ) (v : ℝ≥0) : ℝ :=
  ∑ j ∈ Finset.range n,
    (3 / (((v : ℝ) + (j : ℝ)) * Real.sqrt (2 * Real.pi * ((v : ℝ) + (j : ℝ))))) / 6 *
      (thirdMoment μ + thirdMoment (gaussianReal 0 1))

lemma smoothingError_succ (μ : Measure ℝ) (n : ℕ) (v : ℝ≥0) :
    smoothingError μ (n + 1) v =
      (3 / ((v : ℝ) * Real.sqrt (2 * Real.pi * v))) / 6 *
        (thirdMoment μ + thirdMoment (gaussianReal 0 1)) + smoothingError μ n (v + 1) := by
  unfold smoothingError
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one, Nat.cast_zero, add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [add_assoc, add_left_comm, add_comm]

/-- Quantitative Gaussian-smoothed central limit estimate, proved using an
increasing Gaussian smoothing variance in successive replacements. -/
theorem gaussian_smoothed_sum_comparison {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hsecond : ∫ x, x ^ 2 ∂μ = 1)
    (n : ℕ) {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    |cdf (sumLaw μ n ∗ gaussianReal 0 v) a - cdf (gaussianReal 0 ((n : ℝ≥0) + v)) a| ≤
      smoothingError μ n v := by
  induction n generalizing v a with
  | zero => simp [sumLaw, smoothingError]
  | succ n ih =>
    have hstep (b : ℝ) := gaussian_smoothed_replacement hμ1 hμ2 hμ3 hmean hsecond hv b
    have h1 := cdf_convolution_comparison (ρ := sumLaw μ n) hstep a
    have h2 := ih (v := v + 1) (by positivity) a
    have htri := abs_sub_le
      (cdf (sumLaw μ n ∗ (μ ∗ gaussianReal 0 v)) a)
      (cdf (sumLaw μ n ∗ gaussianReal 0 (v + 1)) a)
      (cdf (gaussianReal 0 ((n : ℝ≥0) + (v + 1))) a)
    have heq : sumLaw μ (n + 1) ∗ gaussianReal 0 v =
        sumLaw μ n ∗ (μ ∗ gaussianReal 0 v) := by
      rw [sumLaw, ← Measure.conv_assoc, Measure.conv_comm μ (sumLaw μ n), Measure.conv_assoc]
    have hvar : ((n + 1 : ℕ) : ℝ≥0) + v = (n : ℝ≥0) + (v + 1) := by push_cast; ring
    rw [heq, hvar, smoothingError_succ]
    linarith only [h1, h2, htri]

lemma inverse_sqrt_step {x : ℝ} (hx : 1 ≤ x) :
    1 / (x * Real.sqrt x) ≤ 4 * ((Real.sqrt x)⁻¹ - (Real.sqrt (x + 1))⁻¹) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hA : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hB : 0 < Real.sqrt (x + 1) := by positivity
  have hsA := Real.sq_sqrt hxp.le
  have hsB := Real.sq_sqrt (show 0 ≤ x + 1 by positivity)
  have hab : Real.sqrt (x + 1) * (Real.sqrt x + Real.sqrt (x + 1)) ≤ 4 * x := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt (x + 1))]
  have hD : 0 < Real.sqrt x * Real.sqrt (x + 1) * (Real.sqrt x + Real.sqrt (x + 1)) := by positivity
  calc
    _ ≤ 4 / (Real.sqrt x * Real.sqrt (x + 1) * (Real.sqrt x + Real.sqrt (x + 1))) := by
      apply (div_le_div_iff₀ (mul_pos hxp hA) hD).mpr
      nlinarith [mul_le_mul_of_nonneg_left hab hA.le]
    _ = _ := by
      field_simp
      nlinarith [hsA, hsB]

lemma sum_inverse_three_halves_le {v : ℝ} (hv : 1 ≤ v) (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / ((v + (j : ℝ)) * Real.sqrt (v + (j : ℝ)))) ≤
      4 / Real.sqrt v := by
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        4 * ((Real.sqrt (v + (j : ℝ)))⁻¹ - (Real.sqrt (v + (j : ℝ) + 1))⁻¹) := by
      apply Finset.sum_le_sum
      intro j _
      exact inverse_sqrt_step (hv.trans (le_add_of_nonneg_right (Nat.cast_nonneg j)))
    _ = 4 * ((Real.sqrt v)⁻¹ - (Real.sqrt (v + (n : ℝ)))⁻¹) := by
      rw [← Finset.mul_sum]
      have hh := Finset.sum_range_sub' (fun j : ℕ ↦ (Real.sqrt (v + (j : ℝ)))⁻¹) n
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at hh
      rw [hh]
    _ ≤ _ := by
      have h : 0 ≤ (Real.sqrt (v + (n : ℝ)))⁻¹ := by positivity
      rw [div_eq_mul_inv]
      linarith

/-- Summing the replacement-dependent smoothing errors gives an error
independent of the number of summands. -/
theorem smoothingError_le {μ : Measure ℝ} {v : ℝ≥0} (hv : 1 ≤ (v : ℝ)) (n : ℕ) :
    smoothingError μ n v ≤
      2 * (thirdMoment μ + thirdMoment (gaussianReal 0 1)) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt (v : ℝ)) := by
  let M : ℝ := thirdMoment μ + thirdMoment (gaussianReal 0 1)
  have hM : 0 ≤ M := add_nonneg (integral_nonneg (fun x ↦ by positivity))
    (integral_nonneg (fun x ↦ by positivity))
  have heq : smoothingError μ n v = M / (2 * Real.sqrt (2 * Real.pi)) *
      ∑ j ∈ Finset.range n, 1 / (((v : ℝ) + (j : ℝ)) * Real.sqrt ((v : ℝ) + (j : ℝ))) := by
    unfold smoothingError
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity)]
    dsimp [M]
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ M / (2 * Real.sqrt (2 * Real.pi)) * (4 / Real.sqrt (v : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_three_halves_le hv n) (by positivity)
    _ = _ := by dsimp [M]; ring

lemma cdf_translate_integrable (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a : ℝ) : Integrable (fun x ↦ cdf ν (a - x)) μ := by
  apply Integrable.of_bound
    (((monotone_cdf ν).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable) 1
  filter_upwards [] with x
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs]
  rw [abs_of_nonneg (cdf_nonneg _ _)]
  exact cdf_le_one _ _

/-- Removing additive smoothing, using only the upper noise tail. -/
lemma cdf_le_smoothed (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a h : ℝ) : cdf μ a ≤ cdf (μ ∗ ν) (a + h) + (1 - cdf ν h) := by
  have hi : Integrable ((Set.Iic a).indicator (fun _ : ℝ ↦ cdf ν h)) μ :=
    (integrable_const _).indicator measurableSet_Iic
  have hp : ∀ x, (Set.Iic a).indicator (fun _ : ℝ ↦ cdf ν h) x ≤ cdf ν (a + h - x) := by
    intro x
    by_cases hx : x ≤ a
    · rw [Set.indicator_of_mem (show x ∈ Set.Iic a from hx)]
      exact monotone_cdf ν (by linarith)
    · rw [Set.indicator_of_notMem (show x ∉ Set.Iic a from hx)]
      exact cdf_nonneg _ _
  have hh := integral_mono hi (cdf_translate_integrable μ ν (a + h)) hp
  rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, ← cdf_eq_real,
    ← cdf_conv] at hh
  have hprod := mul_nonneg (sub_nonneg.mpr (cdf_le_one μ a)) (sub_nonneg.mpr (cdf_le_one ν h))
  nlinarith only [hh, hprod]

/-- Removing additive smoothing, using only the lower noise tail. -/
lemma smoothed_cdf_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a h : ℝ) : cdf (μ ∗ ν) (a - h) ≤ cdf μ a + cdf ν (-h) := by
  have hi : Integrable ((Set.Iic a).indicator (fun _ : ℝ ↦ (1 : ℝ))) μ :=
    (integrable_const _).indicator measurableSet_Iic
  have hp : ∀ x, cdf ν (a - h - x) ≤
      (Set.Iic a).indicator (fun _ : ℝ ↦ (1 : ℝ)) x + cdf ν (-h) := by
    intro x
    by_cases hx : x ≤ a
    · rw [Set.indicator_of_mem (show x ∈ Set.Iic a from hx)]
      exact (cdf_le_one _ _).trans (le_add_of_nonneg_right (cdf_nonneg _ _))
    · rw [Set.indicator_of_notMem (show x ∉ Set.Iic a from hx), zero_add]
      exact monotone_cdf ν (by linarith)
  have hh := integral_mono (cdf_translate_integrable μ ν (a - h)) (hi.add (integrable_const _)) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add hi (integrable_const _), integral_indicator_const 1 measurableSet_Iic,
    integral_const, measureReal_univ_eq_one, one_smul, smul_eq_mul, mul_one, ← cdf_eq_real,
    ← cdf_conv] at hh
  exact hh

lemma gaussian_cdf_noise_tails (v : ℝ≥0) {h : ℝ} (hh : 0 < h) :
    1 - cdf (gaussianReal 0 v) h ≤ (v : ℝ) / h ^ 2 ∧
      cdf (gaussianReal 0 v) (-h) ≤ (v : ℝ) / h ^ 2 := by
  have hc := meas_ge_le_variance_div_sq (memLp_id_gaussianReal (μ := 0) (v := v) 2) hh
  rw [variance_id_gaussianReal] at hc
  simp only [id_eq, integral_id_gaussianReal, sub_zero] at hc
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  change (gaussianReal 0 v).real {x | h ≤ |x|} ≤ _ at hr
  constructor
  · have hsub : (Set.Iic h)ᶜ ⊆ {x : ℝ | h ≤ |x|} := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Iic, not_le] at hx
      exact hx.le.trans (le_abs_self x)
    have hcomp := measureReal_compl (μ := gaussianReal 0 v) (s := Set.Iic h) measurableSet_Iic
    simp only [measureReal_univ_eq_one] at hcomp
    rw [cdf_eq_real, ← hcomp]
    exact (measureReal_mono hsub).trans hr
  · rw [cdf_eq_real]
    refine (measureReal_mono ?_).trans hr
    intro x hx
    simp only [Set.mem_Iic, Set.mem_setOf_eq] at hx ⊢
    linarith [neg_le_abs x]

lemma gaussian_cdf_modulus {v : ℝ≥0} (hv : v ≠ 0) (a b : ℝ) :
    |cdf (gaussianReal 0 v) b - cdf (gaussianReal 0 v) a| ≤
      |b - a| / Real.sqrt (2 * Real.pi * v) := by
  have hp (x : ℝ) : ‖deriv (cdf (gaussianReal 0 v)) x‖ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    rw [gaussian_cdf_deriv hv, Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    unfold gaussianPDFReal
    apply mul_le_of_le_one_right (by positivity)
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (𝕜 := ℝ) (f := (cdf (gaussianReal 0 v) : ℝ → ℝ))
    (fun x _ ↦ (gaussian_cdf_hasDerivAt hv x).differentiableAt)
    (fun x _ ↦ hp x) convex_univ (x := a) (y := b) (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using hm

/-- A deterministic smoothing inequality for CDF comparison. The reference
modulus and the two noise tails are kept explicit. -/
theorem cdf_unsmoothing_bound {μ ν ρ : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {h E Q L : ℝ} (hh : 0 < h)
    (hq : 1 - cdf ρ h ≤ Q ∧ cdf ρ (-h) ≤ Q)
    (hsm : ∀ b, |cdf (μ ∗ ρ) b - cdf (ν ∗ ρ) b| ≤ E)
    (hmod : ∀ a b, |cdf ν b - cdf ν a| ≤ L * |b - a|) (a : ℝ) :
    |cdf μ a - cdf ν a| ≤ E + 2 * Q + 2 * L * h := by
  have hup := cdf_le_smoothed μ ρ a h
  have hlow := smoothed_cdf_le μ ρ a h
  have hnup := smoothed_cdf_le ν ρ (a + 2 * h) h
  have hnlow := cdf_le_smoothed ν ρ (a - 2 * h) h
  rw [show a + 2 * h - h = a + h by ring] at hnup
  rw [show a - 2 * h + h = a - h by ring] at hnlow
  have hsp := abs_le.mp (hsm (a + h))
  have hsn := abs_le.mp (hsm (a - h))
  have hmp := hmod a (a + 2 * h)
  have hmn := hmod a (a - 2 * h)
  rw [show a + 2 * h - a = 2 * h by ring, abs_of_pos (by positivity : 0 < 2 * h)] at hmp
  rw [show a - 2 * h - a = -(2 * h) by ring, abs_neg,
    abs_of_pos (by positivity : 0 < 2 * h)] at hmn
  have hp := abs_le.mp hmp
  have hn := abs_le.mp hmn
  apply abs_le.mpr
  constructor <;> nlinarith only [hup, hlow, hnup, hnlow, hsp.1, hsp.2, hsn.1, hsn.2, hp.1, hp.2, hn.1, hn.2, hq.1, hq.2]

/-- A proved quantitative CDF bound for standardized iid sums. The smoothing
variance `v` and removal distance `h` can be optimized afterward. -/
theorem cdf_sum_normal_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hsecond : ∫ x, x ^ 2 ∂μ = 1)
    (n : ℕ) (hn : 0 < n) {v : ℝ≥0} (hv : 1 ≤ (v : ℝ)) {h : ℝ} (hh : 0 < h) (a : ℝ) :
    |cdf (sumLaw μ n) a - cdf (gaussianReal 0 (n : ℝ≥0)) a| ≤
      2 * (thirdMoment μ + thirdMoment (gaussianReal 0 1)) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt (v : ℝ)) +
      2 * (v : ℝ) / h ^ 2 + 2 * h / Real.sqrt (2 * Real.pi * (n : ℝ)) := by
  have hvp : 0 < (v : ℝ) := lt_of_lt_of_le zero_lt_one hv
  have hvnz : v ≠ 0 := by exact_mod_cast hvp.ne'
  have hnnz : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsm (b : ℝ) :
      |cdf (sumLaw μ n ∗ gaussianReal 0 v) b - cdf (gaussianReal 0 (n : ℝ≥0) ∗ gaussianReal 0 v) b| ≤
      2 * (thirdMoment μ + thirdMoment (gaussianReal 0 1)) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt (v : ℝ)) := by
    rw [gaussianReal_conv_gaussianReal, zero_add]
    exact (gaussian_smoothed_sum_comparison hμ1 hμ2 hμ3 hmean hsecond n hvnz b).trans
      (smoothingError_le hv n)
  have hmod (a b : ℝ) : |cdf (gaussianReal 0 (n : ℝ≥0)) b - cdf (gaussianReal 0 (n : ℝ≥0)) a| ≤
      (Real.sqrt (2 * Real.pi * (n : ℝ)))⁻¹ * |b - a| := by
    simpa only [NNReal.coe_natCast, div_eq_mul_inv, mul_comm] using gaussian_cdf_modulus hnnz a b
  have hb := cdf_unsmoothing_bound hh (gaussian_cdf_noise_tails v hh) hsm hmod a
  convert hb using 1
  ring

/-- The explicit constant in the proved n^(-1/5) CDF estimate. -/
def normalApproximationConstant (M : ℝ) : ℝ :=
  2 * (M + thirdMoment (gaussianReal 0 1)) / Real.sqrt (2 * Real.pi) +
    2 + 2 / Real.sqrt (2 * Real.pi)

/-- A quantitative central limit estimate strong enough for the full
Cramér–Petrov range. It is uniform in the CDF argument and depends only on the
absolute third moment of the standardized law. -/
theorem cdf_sum_normal_rate {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hsecond : ∫ x, x ^ 2 ∂μ = 1)
    (n : ℕ) (hn : 0 < n) (a : ℝ) :
    |cdf (sumLaw μ n) a - cdf (gaussianReal 0 (n : ℝ≥0)) a| ≤
      normalApproximationConstant (thirdMoment μ) * (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  let v : ℝ≥0 := ⟨(n : ℝ) ^ (2 / 5 : ℝ), Real.rpow_nonneg hnp.le _⟩
  let h : ℝ := (n : ℝ) ^ (3 / 10 : ℝ)
  have hv : 1 ≤ (v : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hh : 0 < h := Real.rpow_pos_of_pos hnp _
  have hb := cdf_sum_normal_bound hμ1 hμ2 hμ3 hmean hsecond n hn hv hh a
  have hvroot : Real.sqrt (v : ℝ) = (n : ℝ) ^ (1 / 5 : ℝ) := by
    dsimp [v]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnp.le]
    norm_num
  have hpow2 : h ^ 2 = (n : ℝ) ^ (3 / 5 : ℝ) := by
    dsimp [h]
    rw [← Real.rpow_mul_natCast hnp.le]
    norm_num
  have hvdiv : (v : ℝ) / h ^ 2 = (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
    rw [hpow2]
    dsimp [v]
    rw [← Real.rpow_sub hnp]
    norm_num
  have hhdiv : h / Real.sqrt (n : ℝ) = (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
    dsimp [h]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hnp]
    norm_num
  have hfirst :
      2 * (thirdMoment μ + thirdMoment (gaussianReal 0 1)) /
        (Real.sqrt (2 * Real.pi) * Real.sqrt (v : ℝ)) =
      (2 * (thirdMoment μ + thirdMoment (gaussianReal 0 1)) / Real.sqrt (2 * Real.pi)) *
        (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
    rw [hvroot, Real.rpow_neg hnp.le]
    ring
  have hsecondterm : 2 * (v : ℝ) / h ^ 2 = 2 * (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
    rw [mul_div_assoc, hvdiv]
  have hthird : 2 * h / Real.sqrt (2 * Real.pi * (n : ℝ)) =
      (2 / Real.sqrt (2 * Real.pi)) * (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
    rw [Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity)]
    calc
      _ = (2 / Real.sqrt (2 * Real.pi)) * (h / Real.sqrt (n : ℝ)) := by ring
      _ = _ := by rw [hhdiv]
  rw [hfirst, hsecondterm, hthird] at hb
  convert hb using 1
  unfold normalApproximationConstant
  ring

/-- Uniform version when only a common third-moment budget is specified. -/
theorem cdf_sum_normal_rate_of_third_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hsecond : ∫ x, x ^ 2 ∂μ = 1)
    {M : ℝ} (hM : thirdMoment μ ≤ M) (n : ℕ) (hn : 0 < n) (a : ℝ) :
    |cdf (sumLaw μ n) a - cdf (gaussianReal 0 (n : ℝ≥0)) a| ≤
      normalApproximationConstant M * (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
  apply (cdf_sum_normal_rate hμ1 hμ2 hμ3 hmean hsecond n hn a).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  unfold normalApproximationConstant
  gcongr

end GaussianTilt.GaussianSmoothing
