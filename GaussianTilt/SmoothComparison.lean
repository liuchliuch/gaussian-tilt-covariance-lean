import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smooth replacement estimates

Quantitative, proved analytic input for shrinking-band normal comparison.
No central limit theorem is assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.SmoothComparison

/-- A global third-derivative bound controls the Taylor remainder, first on an
ordered interval. -/
lemma taylor_two_remainder_of_lt {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {C a b : ℝ} (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (hab : a < b) :
    |f b - (f a + deriv f a * (b - a) + iteratedDeriv 2 f a * (b - a) ^ 2 / 2)| ≤
      C * |b - a| ^ 3 / 6 := by
  obtain ⟨u, hu, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hab hf.contDiffOn
  have hpoly : taylorWithinEval f 2 (Set.Icc a b) a b =
      f a + deriv f a * (b - a) + iteratedDeriv 2 f a * (b - a) ^ 2 / 2 := by
    rw [taylor_within_apply]
    have hh (k : ℕ) (hk : k ≤ 2) :
        iteratedDerivWithin k f (Set.Icc a b) a = iteratedDeriv k f a := by
      apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      · exact hf.contDiffAt.of_le (by exact_mod_cast hk.trans (by norm_num : 2 ≤ 3))
      · exact ⟨le_rfl, hab.le⟩
    norm_num [Finset.sum_range_succ, hh 0 (by norm_num), hh 1 (by norm_num),
      hh 2 (by norm_num), iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul]
    ring
  rw [hpoly] at he
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num [Nat.factorial]
  gcongr
  exact hC u

/-- A global third-derivative bound controls the Taylor remainder in either
orientation. -/
theorem taylor_two_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {C : ℝ} (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (a b : ℝ) :
    |f b - (f a + deriv f a * (b - a) + iteratedDeriv 2 f a * (b - a) ^ 2 / 2)| ≤
      C * |b - a| ^ 3 / 6 := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact taylor_two_remainder_of_lt hf hC hab
  · simp
  · have hneg : ContDiff ℝ 3 (fun x ↦ f (-x)) := hf.comp contDiff_neg
    have hbound : ∀ x, |iteratedDeriv 3 (fun x ↦ f (-x)) x| ≤ C := by
      intro x
      simpa [iteratedDeriv_comp_neg, smul_eq_mul] using hC (-x)
    have h := taylor_two_remainder_of_lt hneg hbound (a := -a) (b := -b) (by linarith)
    simp only [iteratedDeriv_comp_neg, smul_eq_mul, deriv_comp_neg, neg_neg] at h
    have hd : -b - -a = -(b - a) := by ring
    rw [hd, abs_neg] at h
    convert h using 1
    congr 1
    ring

/-- Absolute third moment, used only when the integral is finite. -/
def thirdMoment (μ : Measure ℝ) : ℝ := ∫ x, |x| ^ 3 ∂μ

/-- One replacement step: matching first and second moments cancels the entire
quadratic Taylor polynomial, leaving an explicit third-moment error. -/
theorem one_step_replacement {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {B C : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C)
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ) (hν1 : Integrable (fun x : ℝ ↦ x) ν)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ) (hν2 : Integrable (fun x : ℝ ↦ x ^ 2) ν)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hν3 : Integrable (fun x : ℝ ↦ |x| ^ 3) ν)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν)
    (hsecond : ∫ x, x ^ 2 ∂μ = ∫ x, x ^ 2 ∂ν) (z : ℝ) :
    |(∫ x, f (z + x) ∂μ) - ∫ x, f (z + x) ∂ν| ≤
      C / 6 * (thirdMoment μ + thirdMoment ν) := by
  let P : ℝ → ℝ := fun x ↦ f z + deriv f z * x + iteratedDeriv 2 f z * x ^ 2 / 2
  have hPμ : Integrable P μ := by
    convert ((integrable_const (f z)).add (hμ1.const_mul (deriv f z))).add
      (hμ2.const_mul (iteratedDeriv 2 f z / 2)) using 1
    ext x
    dsimp [P]
    ring
  have hPν : Integrable P ν := by
    convert ((integrable_const (f z)).add (hν1.const_mul (deriv f z))).add
      (hν2.const_mul (iteratedDeriv 2 f z / 2)) using 1
    ext x
    dsimp [P]
    ring
  have hfμ : Integrable (fun x ↦ f (z + x)) μ := by
    apply Integrable.of_bound (hf.continuous.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable B
    exact ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs] using hB (z + x))
  have hfν : Integrable (fun x ↦ f (z + x)) ν := by
    apply Integrable.of_bound (hf.continuous.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable B
    exact ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs] using hB (z + x))
  have hP : ∫ x, P x ∂μ = ∫ x, P x ∂ν := by
    have heq : P = fun x ↦ (f z + deriv f z * x) + (iteratedDeriv 2 f z / 2) * x ^ 2 := by
      ext x
      dsimp [P]
      ring
    have hlinμ : Integrable (fun x : ℝ ↦ f z + deriv f z * x) μ :=
      (integrable_const _).add (hμ1.const_mul _)
    have hlinν : Integrable (fun x : ℝ ↦ f z + deriv f z * x) ν :=
      (integrable_const _).add (hν1.const_mul _)
    rw [heq, integral_add hlinμ (hμ2.const_mul _), integral_add hlinν (hν2.const_mul _),
      integral_add (integrable_const _) (hμ1.const_mul _),
      integral_add (integrable_const _) (hν1.const_mul _)]
    simp only [integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul, hsecond]
    rw [integral_const_mul (deriv f z) (fun x : ℝ ↦ x),
      integral_const_mul (deriv f z) (fun x : ℝ ↦ x), hmean]
  have hrem (x : ℝ) : ‖f (z + x) - P x‖ ≤ C / 6 * |x| ^ 3 := by
    have h := taylor_two_remainder hf hC z (z + x)
    simpa [P, Real.norm_eq_abs, mul_div_right_comm] using h
  have hm := norm_integral_le_integral_norm (f := fun x ↦ f (z + x) - P x) (μ := μ)
  have hn := norm_integral_le_integral_norm (f := fun x ↦ f (z + x) - P x) (μ := ν)
  have hm' := integral_mono ((hfμ.sub hPμ).norm) (hμ3.const_mul (C / 6)) hrem
  have hn' := integral_mono ((hfν.sub hPν).norm) (hν3.const_mul (C / 6)) hrem
  rw [integral_const_mul] at hm' hn'
  rw [integral_sub hfμ hPμ, Real.norm_eq_abs] at hm
  rw [integral_sub hfν hPν, Real.norm_eq_abs] at hn
  have htri := abs_sub_le ((∫ x, f (z + x) ∂μ)) ((∫ x, P x ∂μ)) ((∫ x, f (z + x) ∂ν))
  rw [hP, abs_sub_comm (∫ x, P x ∂ν)] at htri
  simp only [Pi.sub_apply] at hm' hn'
  rw [hP] at hm
  dsimp [thirdMoment]
  nlinarith only [hm, hn, hm', hn', htri]

/-- The law of a sum of independent variables with common law `μ`. -/
def sumLaw (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => μ ∗ sumLaw μ n

instance sumLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (sumLaw μ n) := by
  induction n with
  | zero => simp only [sumLaw]; infer_instance
  | succ n ih => simp only [sumLaw]; infer_instance

lemma integral_conv_bounded {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (z : ℝ) :
    (∫ x, f (z + x) ∂(μ ∗ ν)) = ∫ x, ∫ y, f (z + (x + y)) ∂ν ∂μ := by
  have hi : Integrable (fun p : ℝ × ℝ ↦ f (z + (p.1 + p.2))) (μ.prod ν) := by
    apply Integrable.of_bound (hf.comp (measurable_const.add (measurable_fst.add measurable_snd))).aestronglyMeasurable B
    exact ae_of_all _ (fun p ↦ by simpa only [Real.norm_eq_abs] using hB (z + (p.1 + p.2)))
  have hfm : Measurable (fun x : ℝ ↦ f (z + x)) :=
    hf.comp (measurable_const.add measurable_id)
  rw [Measure.conv, integral_map (by fun_prop) hfm.aestronglyMeasurable, integral_prod _ hi]

/-- Smoothing both measures by the same independent law cannot increase a
uniform translated-test-function comparison error. -/
lemma convolution_comparison {μ ν ρ : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {f : ℝ → ℝ} (hf : Measurable f) {B E : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hE : ∀ z, |(∫ x, f (z + x) ∂μ) - ∫ x, f (z + x) ∂ν| ≤ E) (z : ℝ) :
    |(∫ x, f (z + x) ∂(ρ ∗ μ)) - ∫ x, f (z + x) ∂(ρ ∗ ν)| ≤ E := by
  have hiμ : Integrable (fun p : ℝ × ℝ ↦ f (z + (p.1 + p.2))) (ρ.prod μ) := by
    apply Integrable.of_bound (hf.comp (measurable_const.add (measurable_fst.add measurable_snd))).aestronglyMeasurable B
    exact ae_of_all _ (fun p ↦ by simpa only [Real.norm_eq_abs] using hB (z + (p.1 + p.2)))
  have hiν : Integrable (fun p : ℝ × ℝ ↦ f (z + (p.1 + p.2))) (ρ.prod ν) := by
    apply Integrable.of_bound (hf.comp (measurable_const.add (measurable_fst.add measurable_snd))).aestronglyMeasurable B
    exact ae_of_all _ (fun p ↦ by simpa only [Real.norm_eq_abs] using hB (z + (p.1 + p.2)))
  rw [integral_conv_bounded hf hB z, integral_conv_bounded hf hB z,
    ← integral_sub hiμ.integral_prod_left hiν.integral_prod_left, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := ρ)
    (f := fun y ↦ (∫ x, f (z + (y + x)) ∂μ) - ∫ x, f (z + (y + x)) ∂ν)
    (C := E) (ae_of_all _ (fun y ↦ by simpa [Real.norm_eq_abs, add_assoc] using hE (z + y)))
  simpa only [measureReal_univ_eq_one, mul_one] using h

/-- Finite Lindeberg replacement for actual convolution powers. The bound is
linear in the number of summands and the absolute third moments. -/
theorem smooth_sum_comparison {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {B C : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C)
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ) (hν1 : Integrable (fun x : ℝ ↦ x) ν)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ) (hν2 : Integrable (fun x : ℝ ↦ x ^ 2) ν)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hν3 : Integrable (fun x : ℝ ↦ |x| ^ 3) ν)
    (hmean : ∫ x, x ∂μ = ∫ x, x ∂ν)
    (hsecond : ∫ x, x ^ 2 ∂μ = ∫ x, x ^ 2 ∂ν) (n : ℕ) (z : ℝ) :
    |(∫ x, f (z + x) ∂sumLaw μ n) - ∫ x, f (z + x) ∂sumLaw ν n| ≤
      (n : ℝ) * (C / 6 * (thirdMoment μ + thirdMoment ν)) := by
  let E : ℝ := C / 6 * (thirdMoment μ + thirdMoment ν)
  have hstep (z : ℝ) : |(∫ x, f (z + x) ∂μ) - ∫ x, f (z + x) ∂ν| ≤ E :=
    one_step_replacement hf hB hC hμ1 hν1 hμ2 hν2 hμ3 hν3 hmean hsecond z
  induction n generalizing z with
  | zero => simp [sumLaw]
  | succ n ih =>
    have hfirst := convolution_comparison (ρ := sumLaw μ n) hf.continuous.measurable hB hstep z
    rw [Measure.conv_comm (sumLaw μ n) μ, Measure.conv_comm (sumLaw μ n) ν] at hfirst
    have hsecond := convolution_comparison (ρ := ν) hf.continuous.measurable hB ih z
    have htri := abs_sub_le
      (∫ x, f (z + x) ∂(μ ∗ sumLaw μ n))
      (∫ x, f (z + x) ∂(ν ∗ sumLaw μ n))
      (∫ x, f (z + x) ∂(ν ∗ sumLaw ν n))
    simp only [sumLaw, Nat.cast_add, Nat.cast_one]
    change _ ≤ ((n : ℝ) + 1) * E
    change _ ≤ (n : ℝ) * E at hsecond
    nlinarith only [hfirst, hsecond, htri]

lemma sumLaw_gaussian_zero (v : ℝ≥0) (n : ℕ) :
    sumLaw (gaussianReal 0 v) n = gaussianReal 0 ((n : ℝ≥0) * v) := by
  induction n with
  | zero => simp [sumLaw, gaussianReal_zero_var]
  | succ n ih =>
    rw [sumLaw, ih, gaussianReal_conv_gaussianReal]
    congr 1
    · simp
    · push_cast
      ring

lemma gaussian_second_moment (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂gaussianReal 0 v = (v : ℝ) := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  rw [variance_id_gaussianReal] at h
  simpa only [Pi.pow_apply, id_eq, integral_id_gaussianReal, zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h.symm

lemma gaussian_third_moment_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ ↦ |x| ^ 3) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := v) 3).integrable_norm_pow' (p := 3)
  simpa only [id_eq, Real.norm_eq_abs] using h

/-- Quantitative smooth comparison with the actual Gaussian law of the matching
variance. All Gaussian moments and the Gaussian sum law are discharged here. -/
theorem smooth_normal_comparison {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {B C : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C)
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (v : ℝ≥0)
    (hsecond : ∫ x, x ^ 2 ∂μ = (v : ℝ)) (n : ℕ) (z : ℝ) :
    |(∫ x, f (z + x) ∂sumLaw μ n) - ∫ x, f (z + x) ∂gaussianReal 0 ((n : ℝ≥0) * v)| ≤
      (n : ℝ) * (C / 6 * (thirdMoment μ + thirdMoment (gaussianReal 0 v))) := by
  have hν1 : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hν2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have h := smooth_sum_comparison hf hB hC hμ1 hν1 hμ2 hν2 hμ3
    (gaussian_third_moment_integrable v)
    (hmean.trans integral_id_gaussianReal.symm)
    (hsecond.trans (gaussian_second_moment v).symm) n z
  rwa [sumLaw_gaussian_zero] at h

end GaussianTilt.SmoothComparison
