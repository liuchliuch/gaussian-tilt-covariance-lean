import GaussianTilt.ScalarLogConcaveMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace GaussianTilt.ScalarLogConcaveMoments

lemma tail_power_exponential_bound {p t : ℝ} (hp : 2 ≤ p) (ht : 0 ≤ t) :
    6 * Real.exp (-t / 4) * t ^ (p - 1) ≤
      (6 * (8 * p) ^ (p - 1)) * Real.exp ((-1 / 8) * t) := by
  have hq : 0 ≤ p - 1 := by linarith
  have h := ProbabilityTheory.rpow_abs_le_mul_max_exp_of_pos t hq (by norm_num : (0 : ℝ) < 1 / 8)
  rw [abs_of_nonneg ht, max_eq_left (Real.exp_le_exp.mpr (by linarith))] at h
  have hc : ((p - 1) / (1 / 8)) ^ (p - 1) ≤ (8 * p) ^ (p - 1) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hq
  have hb := h.trans (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _))
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 6 * Real.exp (-t / 4) by positivity)
  apply hb'.trans_eq
  rw [mul_assoc, mul_left_comm (Real.exp (-t / 4)), ← mul_assoc,
    ← Real.exp_add]
  congr 2
  ring

lemma lintegral_exp_neg_eighth :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp ((-1 / 8) * t))) = ENNReal.ofReal 8 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 8 : ℝ) < 0) 0)
    (Eventually.of_forall (fun t ↦ (Real.exp_pos _).le)),
    integral_exp_mul_Ioi (by norm_num : (-1 / 8 : ℝ) < 0) 0]
  norm_num

lemma moment_constant_bound {p : ℝ} (hp : 2 ≤ p) :
    p * (6 * (8 * p) ^ (p - 1)) * 8 ≤ (48 * p) ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have h6 : (6 : ℝ) ≤ 6 ^ p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) hp1
  calc
    p * (6 * (8 * p) ^ (p - 1)) * 8 = 6 * (8 * p) ^ p := by
      rw [Real.rpow_sub (by positivity : 0 < 8 * p), Real.rpow_one]
      field_simp
    _ ≤ (6 : ℝ) ^ p * (8 * p) ^ p := mul_le_mul_of_nonneg_right h6 (by positivity)
    _ = (48 * p) ^ p := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity)]
      congr 1
      ring

/-- Exponential tails imply genuine integrability and the linear real-order
moment estimate. The underlying measure need not be normalized. -/
theorem moment_of_exponential_tail (μ : Measure ℝ)
    (htail : ∀ t : ℝ, 0 < t → μ {x : ℝ | t < |x|} ≤ ENNReal.ofReal (6 * Real.exp (-t / 4)))
    {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun x : ℝ ↦ |x| ^ p) μ ∧
      (∫ x : ℝ, |x| ^ p ∂μ) ^ (1 / p) ≤ 48 * p := by
  have hp0 : 0 < p := by linarith
  have hqm : Measurable (fun x : ℝ ↦ |x| ^ p) := by fun_prop
  have hqn : ∀ x : ℝ, 0 ≤ |x| ^ p := fun x ↦ Real.rpow_nonneg (abs_nonneg x) p
  have hL : (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ p) ∂μ) ≤ ENNReal.ofReal ((48 * p) ^ p) := by
    rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ
      (Eventually.of_forall (fun x : ℝ ↦ abs_nonneg x)) measurable_abs.aemeasurable hp0]
    calc
      _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (6 * (8 * p) ^ (p - 1)) *
            ENNReal.ofReal (Real.exp ((-1 / 8) * t)) := by
        apply mul_le_mul_left'
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        calc
          μ {x : ℝ | t < |x|} * ENNReal.ofReal (t ^ (p - 1)) ≤
              ENNReal.ofReal (6 * Real.exp (-t / 4)) * ENNReal.ofReal (t ^ (p - 1)) :=
            mul_le_mul_right' (htail t ht0) _
          _ = ENNReal.ofReal (6 * Real.exp (-t / 4) * t ^ (p - 1)) :=
            (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ ENNReal.ofReal ((6 * (8 * p) ^ (p - 1)) * Real.exp ((-1 / 8) * t)) :=
            ENNReal.ofReal_le_ofReal (tail_power_exponential_bound hp ht0.le)
          _ = _ := ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (p * (6 * (8 * p) ^ (p - 1)) * 8) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_exp_neg_eighth,
          ← mul_assoc, ← ENNReal.ofReal_mul hp0.le, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (moment_constant_bound hp)
  have hi : Integrable (fun x : ℝ ↦ |x| ^ p) μ :=
    ⟨hqm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hqn)).mpr
      (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hqn)] at hL
  have hb := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (48 * p) ^ p)).mp hL
  have hr := Real.rpow_le_rpow (integral_nonneg hqn) hb (by positivity : 0 ≤ 1 / p)
  rwa [← Real.rpow_mul (by positivity : 0 ≤ 48 * p), mul_one_div_cancel hp0.ne', Real.rpow_one] at hr

lemma abs_tail_integral {f : ℝ → ℝ} (hi : Integrable f) (he : ∀ x, f (-x) = f x)
    {t : ℝ} (ht : 0 ≤ t) : (∫ x in {x : ℝ | t < |x|}, f x) = 2 * tail f t := by
  have hs : {x : ℝ | t < |x|} = Iio (-t) ∪ Ioi t := by
    ext x
    simp only [mem_setOf_eq, lt_abs, mem_union, mem_Iio, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hd : Disjoint (Iio (-t)) (Ioi t) := by
    rw [disjoint_left]
    intro x hx hy
    change x < -t at hx
    change t < x at hy
    linarith
  rw [hs, setIntegral_union hd measurableSet_Ioi hi.integrableOn hi.integrableOn,
    ← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi t f]
  simp only [he, tail]
  ring

/-- The density law's two-sided exponential tail is proved from scalar
logconcavity, evenness, total mass and the second moment. -/
theorem density_abs_tail_le {f : ℝ → ℝ} (hf : LogConcaveMarginal.IsLogConcave f)
    (hm : Measurable f) (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0)
    (he : ∀ x, f (-x) = f x) (hmass : ∫ x, f x = 1)
    (hv : ∫ x, x ^ 2 * f x = 1) {t : ℝ} (ht : 0 ≤ t) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) {x : ℝ | t < |x|} ≤
      ENNReal.ofReal (6 * Real.exp (-t / 4)) := by
  have hi := LogConcaveMarginal.integrable_of_compact_support hf hm hs
  rw [withDensity_apply _ (measurableSet_lt measurable_const measurable_abs),
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (Eventually.of_forall hf.1),
    abs_tail_integral hi he ht]
  apply ENNReal.ofReal_le_ofReal
  linarith [tail_le_exp hf hm hs he hmass hv ht]

/-- Compactness and measurable logconcavity provide the weighted real moments
as actual integrable functions, independently of the numerical estimate. -/
lemma density_abs_rpow_integrable {f : ℝ → ℝ} (hf : LogConcaveMarginal.IsLogConcave f)
    (hm : Measurable f) (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0)
    {p : ℝ} (hp : 0 ≤ p) : Integrable (fun x : ℝ ↦ |x| ^ p * f x) := by
  apply integrable_continuous_mul (LogConcaveMarginal.integrable_of_compact_support hf hm hs) _ hs
  exact continuous_abs.rpow_const (fun x ↦ Or.inr hp)

/-- The genuine one-dimensional weak-moment inequality, with the explicit
universal constant `48`, for every real order at least two. -/
theorem even_logconcave_moment_le {f : ℝ → ℝ} (hf : LogConcaveMarginal.IsLogConcave f)
    (hm : Measurable f) (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0)
    (he : ∀ x, f (-x) = f x) (hmass : ∫ x, f x = 1)
    (hv : ∫ x, x ^ 2 * f x = 1) {p : ℝ} (hp : 2 ≤ p) :
    (∫ x : ℝ, |x| ^ p * f x) ^ (1 / p) ≤ 48 * p := by
  have h := (moment_of_exponential_tail
    (volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (fun t ht ↦ density_abs_tail_le hf hm hs he hmass hv ht.le) hp).2
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Eventually.of_forall (fun x ↦ ENNReal.ofReal_lt_top))] at h
  simpa only [ENNReal.toReal_ofReal (hf.1 _), smul_eq_mul, mul_comm (f _)] using h

end GaussianTilt.ScalarLogConcaveMoments
