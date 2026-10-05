import GaussianTilt.SmoothComparison
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Smooth cutoffs for the one-sided Laplace transform

The cutoff is explicit and its regularity and derivative bound are proved.
Together with the finite replacement estimate, this supplies a shrinking-scale
normal comparison without assuming a central limit theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.LaplaceCutoff
open SmoothComparison

/-- A smooth minorant of the one-sided exponential kernel. -/
def cutoff (x : ℝ) : ℝ := Real.smoothTransition x * Real.exp (-x)

lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ n cutoff :=
  Real.smoothTransition.contDiff.mul (contDiff_exp.comp contDiff_neg)

lemma cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x :=
  mul_nonneg (Real.smoothTransition.nonneg x) (Real.exp_nonneg _)

lemma cutoff_zero {x : ℝ} (hx : x ≤ 0) : cutoff x = 0 := by
  simp [cutoff, Real.smoothTransition.zero_of_nonpos hx]

lemma cutoff_eq_exp {x : ℝ} (hx : 1 ≤ x) : cutoff x = Real.exp (-x) := by
  simp [cutoff, Real.smoothTransition.one_of_one_le hx]

lemma cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := by
  by_cases hx : x ≤ 0
  · rw [cutoff_zero hx]; norm_num
  · have hp : 0 ≤ x := (not_le.mp hx).le
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (Real.smoothTransition.le_one x)).trans
      (Real.exp_le_one_iff.mpr (by linarith))

lemma cutoff_abs_le_one (x : ℝ) : |cutoff x| ≤ 1 := by
  rw [abs_of_nonneg (cutoff_nonneg x)]
  exact cutoff_le_one x

lemma cutoff_le_exp (x : ℝ) : cutoff x ≤ Real.exp (-x) :=
  mul_le_of_le_one_left (Real.exp_nonneg _) (Real.smoothTransition.le_one x)

/-- The cutoff really has a finite global third-derivative bound; this is not
an input assumption to the normal comparison. -/
theorem cutoff_third_derivative_bounded :
    ∃ C > 0, ∀ x, |iteratedDeriv 3 cutoff x| ≤ C := by
  have hc : Continuous (iteratedDeriv 3 cutoff) :=
    (cutoff_contDiff 3).continuous_iteratedDeriv 3 le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 2) hc.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x ↦ ?_⟩
  by_cases hx0 : x < 0
  · have he : cutoff =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hx0] with y hy
      exact cutoff_zero hy.le
    rw [he.iteratedDeriv_eq 3]
    norm_num [iteratedDeriv_succ, iteratedDeriv_zero]
  by_cases hx2 : x ≤ 2
  · exact (hC x ⟨le_of_not_gt hx0, hx2⟩).trans (le_max_left _ _)
  · have hx1 : 1 < x := by linarith [not_le.mp hx2]
    have he : cutoff =ᶠ[𝓝 x] (fun y ↦ Real.exp ((-1 : ℝ) * y)) := by
      filter_upwards [Ioi_mem_nhds hx1] with y hy
      simpa using cutoff_eq_exp hy.le
    rw [he.iteratedDeriv_eq 3, iteratedDeriv_exp_const_mul]
    simp only [show (-1 : ℝ) ^ 3 = -1 by norm_num, neg_one_mul, abs_neg, Real.abs_exp]
    exact (Real.exp_le_one_iff.mpr (show -x ≤ 0 by linarith)).trans (le_max_right _ _)

lemma cutoff_integrable : Integrable cutoff := by
  have hg : Integrable ((Set.Ioi (0 : ℝ)).indicator (fun x ↦ Real.exp (-x))) :=
    (integrableOn_exp_neg_Ioi 0).integrable_indicator measurableSet_Ioi
  apply hg.mono' (cutoff_contDiff 3).continuous.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg x)]
  by_cases hx : 0 < x
  · simpa [hx] using cutoff_le_exp x
  · simp [hx, cutoff_zero (le_of_not_gt hx)]

lemma integral_cutoff_le_one : ∫ x, cutoff x ≤ (1 : ℝ) := by
  have hg : Integrable ((Set.Ioi (0 : ℝ)).indicator (fun x ↦ Real.exp (-x))) :=
    (integrableOn_exp_neg_Ioi 0).integrable_indicator measurableSet_Ioi
  calc
    _ ≤ ∫ x, (Set.Ioi (0 : ℝ)).indicator (fun y ↦ Real.exp (-y)) x := by
      apply integral_mono cutoff_integrable hg
      intro x
      by_cases hx : 0 < x
      · simpa [hx] using cutoff_le_exp x
      · simp [hx, cutoff_zero (le_of_not_gt hx)]
    _ = 1 := by rw [integral_indicator measurableSet_Ioi, integral_exp_neg_Ioi_zero]

lemma scaled_cutoff_third_bound {C t : ℝ} (hC : ∀ x, |iteratedDeriv 3 cutoff x| ≤ C)
    (ht : 0 ≤ t) (x : ℝ) :
    |iteratedDeriv 3 (fun y ↦ cutoff (t * y)) x| ≤ C * t ^ 3 := by
  rw [iteratedDeriv_comp_const_mul (cutoff_contDiff 3)]
  simp only [abs_mul, abs_pow, abs_of_nonneg ht]
  nlinarith [mul_le_mul_of_nonneg_left (hC (t * x)) (pow_nonneg ht 3)]

/-- The actual one-sided Laplace transform of a probability measure. -/
def oneSidedLaplace (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x in Set.Ici 0, Real.exp (-t * x) ∂μ

lemma cutoff_sandwich {t : ℝ} (ht : 0 < t) (x : ℝ) :
    cutoff (t * x) ≤ (Set.Ici (0 : ℝ)).indicator (fun y ↦ Real.exp (-t * y)) x ∧
      (Set.Ici (0 : ℝ)).indicator (fun y ↦ Real.exp (-t * y)) x ≤
        Real.exp 1 * cutoff (1 + t * x) := by
  by_cases hx : 0 ≤ x
  · rw [Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
    have htx : 0 ≤ t * x := mul_nonneg ht.le hx
    constructor
    · simpa [neg_mul] using cutoff_le_exp (t * x)
    · rw [cutoff_eq_exp (by linarith : 1 ≤ 1 + t * x), ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      ring_nf
      exact le_rfl
  · have htx : t * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_ge hx)
    rw [Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx), cutoff_zero htx]
    simp only [le_refl, true_and]
    exact mul_nonneg (Real.exp_nonneg _) (cutoff_nonneg _)

lemma oneSidedLaplace_sandwich (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) :
    (∫ x, cutoff (t * x) ∂μ) ≤ oneSidedLaplace μ t ∧
      oneSidedLaplace μ t ≤ Real.exp 1 * ∫ x, cutoff (1 + t * x) ∂μ := by
  have hmeas : Measurable cutoff := (cutoff_contDiff 3).continuous.measurable
  have hlo : Integrable (fun x ↦ cutoff (t * x)) μ := by
    apply Integrable.of_bound (hmeas.comp (measurable_const.mul measurable_id)).aestronglyMeasurable 1
    exact ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs] using cutoff_abs_le_one (t * x))
  have hup : Integrable (fun x ↦ cutoff (1 + t * x)) μ := by
    apply Integrable.of_bound (hmeas.comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable 1
    exact ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs] using cutoff_abs_le_one (1 + t * x))
  have hmid : Integrable ((Set.Ici (0 : ℝ)).indicator (fun x ↦ Real.exp (-t * x))) μ := by
    apply (hup.const_mul (Real.exp 1)).mono'
      ((show Measurable (fun x : ℝ ↦ Real.exp (-t * x)) by fun_prop).aestronglyMeasurable.indicator measurableSet_Ici)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ Real.exp_nonneg _) _)]
    exact (cutoff_sandwich ht x).2
  unfold oneSidedLaplace
  rw [← integral_indicator measurableSet_Ici]
  constructor
  · exact integral_mono hlo hmid (fun x ↦ (cutoff_sandwich ht x).1)
  · rw [← integral_const_mul]
    exact integral_mono hmid (hup.const_mul _) (fun x ↦ (cutoff_sandwich ht x).2)

lemma scaled_cutoff_integrable {t : ℝ} (ht : 0 < t) (z : ℝ) :
    Integrable (fun x : ℝ ↦ cutoff (z + t * x)) :=
  (integrable_comp_mul_left_iff (fun x : ℝ ↦ cutoff (z + x)) ht.ne').mpr
    (cutoff_integrable.comp_add_left z)

lemma integral_scaled_cutoff_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    (∫ x : ℝ, cutoff (z + t * x)) ≤ 1 / t := by
  rw [Measure.integral_comp_mul_left (fun x ↦ cutoff (z + x)) t,
    integral_add_left_eq_self cutoff z, smul_eq_mul, abs_inv, abs_of_pos ht]
  simpa [one_div] using mul_le_mul_of_nonneg_left integral_cutoff_le_one (inv_nonneg.mpr ht.le)

lemma gaussianPDFReal_le_peak (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDFReal
  apply mul_le_of_le_one_right (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

lemma gaussian_cutoff_product_integrable (v : ℝ≥0) {t : ℝ} (ht : 0 < t) (z : ℝ) :
    Integrable (fun x ↦ gaussianPDFReal 0 v x * cutoff (z + t * x)) := by
  apply ((scaled_cutoff_integrable ht z).const_mul (Real.sqrt (2 * Real.pi * v))⁻¹).mono'
    ((measurable_gaussianPDFReal _ _).mul
      ((cutoff_contDiff 3).continuous.measurable.comp
        (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable
  filter_upwards [] with x
  simp only [Function.comp_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (cutoff_nonneg _))]
  exact mul_le_mul_of_nonneg_right (gaussianPDFReal_le_peak v x) (cutoff_nonneg _)

/-- A uniform Gaussian upper estimate, valid at every translate of the cutoff. -/
theorem gaussian_cutoff_upper {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) (z : ℝ) :
    (∫ x, cutoff (z + t * x) ∂gaussianReal 0 v) ≤
      1 / (t * Real.sqrt (2 * Real.pi * v)) := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ x, (Real.sqrt (2 * Real.pi * v))⁻¹ * cutoff (z + t * x) := by
      apply integral_mono (gaussian_cutoff_product_integrable v ht z)
        ((scaled_cutoff_integrable ht z).const_mul _)
      intro x
      exact mul_le_mul_of_nonneg_right (gaussianPDFReal_le_peak v x) (cutoff_nonneg _)
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ * ∫ x, cutoff (z + t * x) := integral_const_mul _ _
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * (1 / t) :=
      mul_le_mul_of_nonneg_left (integral_scaled_cutoff_le ht z) (by positivity)
    _ = _ := by ring

/-- Gaussian mass in a window of width `1/t` yields the correct prefactor.
The condition `1 ≤ v*t²` says that this window is at most a standard deviation. -/
theorem gaussian_cutoff_lower {v : ℝ≥0} {t : ℝ} (ht : 0 < t)
    (hscale : 1 ≤ (v : ℝ) * t ^ 2) :
    Real.exp (-4) / (t * Real.sqrt (2 * Real.pi * v)) ≤
      ∫ x, cutoff (t * x) ∂gaussianReal 0 v := by
  have hvpos : 0 < (v : ℝ) := by
    by_contra h
    have hz : (v : ℝ) = 0 := le_antisymm (le_of_not_gt h) v.coe_nonneg
    rw [hz] at hscale
    norm_num at hscale
  have hv : v ≠ 0 := by exact_mod_cast hvpos.ne'
  have hab : 1 / t ≤ 2 / t := by gcongr; norm_num
  have hprod := gaussian_cutoff_product_integrable v ht 0
  simp only [zero_add] at hprod
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc (1 / t) (2 / t)) :
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-4) ≤
        gaussianPDFReal 0 v x * cutoff (t * x) := by
    have hx0 : 0 ≤ x := (by positivity : 0 ≤ 1 / t).trans hx.1
    have htx1 : 1 ≤ t * x := by nlinarith [(div_le_iff₀ ht).mp hx.1]
    have htx2 : t * x ≤ 2 := by nlinarith [(le_div_iff₀ ht).mp hx.2]
    have hsq : t ^ 2 * x ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (t * x), mul_nonneg (sub_nonneg.mpr htx2) (by positivity : 0 ≤ 2 + t * x)]
    have hxv : x ^ 2 ≤ 4 * (v : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hscale (sq_nonneg x)
      have h2 := mul_le_mul_of_nonneg_left hsq v.coe_nonneg
      nlinarith
    have he : Real.exp (-2) ≤ Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) := by
      apply Real.exp_le_exp.mpr
      apply (le_div_iff₀ (by positivity : 0 < 2 * (v : ℝ))).mpr
      nlinarith
    have hc : Real.exp (-2) ≤ cutoff (t * x) := by
      rw [cutoff_eq_exp htx1]
      exact Real.exp_le_exp.mpr (by linarith)
    unfold gaussianPDFReal
    have hm := mul_le_mul he hc (Real.exp_nonneg _) (Real.exp_nonneg _)
    have he4 : Real.exp (-2) * Real.exp (-2) = Real.exp (-4) := by
      rw [← Real.exp_add]
      norm_num
    rw [he4] at hm
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ by positivity)
    simpa only [mul_assoc] using hh
  have hlocal : (∫ _x : ℝ in Set.Icc (1 / t) (2 / t),
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-4)) ≤
      ∫ x, gaussianPDFReal 0 v x * cutoff (t * x) := by
    exact (setIntegral_mono_on (integrable_const _) hprod.integrableOn measurableSet_Icc hpoint).trans
      (setIntegral_le_integral hprod (ae_of_all _ fun x ↦
        mul_nonneg (gaussianPDFReal_nonneg _ _ _) (cutoff_nonneg _)))
  rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul] at hlocal
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  convert hlocal using 1
  ring

/-- A fixed finite constant, obtained from the proved cutoff regularity. -/
def cutoffDerivativeBound : ℝ := Classical.choose cutoff_third_derivative_bounded

lemma cutoffDerivativeBound_pos : 0 < cutoffDerivativeBound :=
  (Classical.choose_spec cutoff_third_derivative_bounded).1

lemma cutoffDerivativeBound_spec (x : ℝ) :
    |iteratedDeriv 3 cutoff x| ≤ cutoffDerivativeBound :=
  (Classical.choose_spec cutoff_third_derivative_bounded).2 x

/-- Quantitative normal comparison at the shrinking Laplace scale `1/t`.
There is no normal-approximation premise: the error is proved by finite
Lindeberg replacement with the explicit smooth cutoff. -/
theorem oneSidedLaplace_normal_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ1 : Integrable (fun x : ℝ ↦ x) μ)
    (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hμ3 : Integrable (fun x : ℝ ↦ |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (v : ℝ≥0)
    (hsecond : ∫ x, x ^ 2 ∂μ = (v : ℝ)) (n : ℕ) {t : ℝ}
    (ht : 0 < t) (hscale : 1 ≤ (n : ℝ) * (v : ℝ) * t ^ 2) :
    let E := (n : ℝ) * (cutoffDerivativeBound * t ^ 3 / 6 *
      (thirdMoment μ + thirdMoment (gaussianReal 0 v)))
    Real.exp (-4) / (t * Real.sqrt (2 * Real.pi * ((n : ℝ) * (v : ℝ)))) - E ≤
      oneSidedLaplace (sumLaw μ n) t ∧
    oneSidedLaplace (sumLaw μ n) t ≤ Real.exp 1 *
      (1 / (t * Real.sqrt (2 * Real.pi * ((n : ℝ) * (v : ℝ)))) + E) := by
  let f : ℝ → ℝ := fun x ↦ cutoff (t * x)
  have hf : ContDiff ℝ 3 f := (cutoff_contDiff 3).comp (contDiff_const.mul contDiff_id)
  have hB : ∀ x, |f x| ≤ 1 := fun x ↦ cutoff_abs_le_one _
  have hC : ∀ x, |iteratedDeriv 3 f x| ≤ cutoffDerivativeBound * t ^ 3 :=
    scaled_cutoff_third_bound cutoffDerivativeBound_spec ht.le
  have h0 := smooth_normal_comparison hf hB hC hμ1 hμ2 hμ3 hmean v hsecond n 0
  have h1 := smooth_normal_comparison hf hB hC hμ1 hμ2 hμ3 hmean v hsecond n (1 / t)
  have heq (x : ℝ) : t * (1 / t + x) = 1 + t * x := by field_simp
  simp only [f, zero_add] at h0
  simp only [f, heq] at h1
  have hs := oneSidedLaplace_sandwich (sumLaw μ n) ht
  have hv : (n : ℝ≥0) * v ≠ 0 := by
    intro hz
    have hz' : (n : ℝ) * (v : ℝ) = 0 := by exact_mod_cast hz
    rw [hz'] at hscale
    norm_num at hscale
  have hglo := gaussian_cutoff_lower (v := (n : ℝ≥0) * v) ht (by exact_mod_cast hscale)
  have hgup := gaussian_cutoff_upper hv ht 1
  simp only [NNReal.coe_mul, NNReal.coe_natCast] at hglo hgup
  dsimp only
  constructor
  · have he := (abs_le.mp h0).1
    linarith [hs.1]
  · have he := (abs_le.mp h1).2
    have hb : (∫ x, cutoff (1 + t * x) ∂sumLaw μ n) ≤
        1 / (t * Real.sqrt (2 * Real.pi * ((n : ℝ) * (v : ℝ)))) +
          (n : ℝ) * (cutoffDerivativeBound * t ^ 3 / 6 *
            (thirdMoment μ + thirdMoment (gaussianReal 0 v))) := by linarith
    exact hs.2.trans (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))

end GaussianTilt.LaplaceCutoff
