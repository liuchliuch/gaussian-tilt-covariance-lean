import GaussianTilt.LowerProbability
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.Variance

/-!
# Gaussian-window axial marginal

This file proves the one-dimensional analytic implication used in Corollary 4.10.
The acceptance function is an actual measurable function, and all moments below
are Lebesgue integrals. The lower-window hypothesis must be supplied by the
slice-acceptance theorem; it is not asserted here for the constructed body.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set

namespace GaussianTilt
namespace LowerMarginal

/-- Unnormalized density of the axial marginal. -/
def kernel (t : ℝ) (p : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (-t * x ^ 2) * p x

def mass (t : ℝ) (p : ℝ → ℝ) : ℝ := ∫ x, kernel t p x

def secondMomentNumerator (t : ℝ) (p : ℝ → ℝ) : ℝ := ∫ x, x ^ 2 * kernel t p x

lemma kernel_nonneg {t : ℝ} {p : ℝ → ℝ} (hp : ∀ x, 0 ≤ p x) (x : ℝ) :
    0 ≤ kernel t p x := mul_nonneg (Real.exp_nonneg _) (hp x)

lemma kernel_integrable {t : ℝ} (ht : 0 < t) {p : ℝ → ℝ}
    (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1) :
    Integrable (kernel t p) := by
  apply (integrable_exp_neg_mul_sq ht).mono' (by unfold kernel; fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg (fun y ↦ (hp y).1) x)]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (hp x).2

lemma secondMoment_integrable {t : ℝ} (ht : 0 < t) {p : ℝ → ℝ}
    (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x ↦ x ^ 2 * kernel t p x) := by
  have hg : Integrable (fun x : ℝ ↦ x ^ 2 * Real.exp (-t * x ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq ht (s := (2 : ℕ)) (by norm_num))
  apply hg.mono' (by unfold kernel; fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg x)
    (kernel_nonneg (fun y ↦ (hp y).1) x))]
  unfold kernel
  calc
    x ^ 2 * (Real.exp (-t * x ^ 2) * p x) =
        (x ^ 2 * Real.exp (-t * x ^ 2)) * p x := by ring
    _ ≤ x ^ 2 * Real.exp (-t * x ^ 2) :=
      mul_le_of_le_one_right (by positivity) (hp x).2

/-- On the outer half of the Gaussian window the density has a numerical floor. -/
lemma kernel_window_lower {t a : ℝ} (ht : 0 < t) (ha : 0 < a) (hta : t * a ^ 2 = 1)
    {p : ℝ → ℝ} (hw : ∀ x, |x| ≤ a → (1 / 2 : ℝ) ≤ p x)
    {x : ℝ} (hx : x ∈ Icc (a / 2) a) :
    Real.exp (-1) / 2 ≤ kernel t p x := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hxa : |x| ≤ a := by simpa [abs_of_nonneg hx0] using hx.2
  have hsq : x ^ 2 ≤ a ^ 2 := sq_le_sq' (by linarith [hx.1]) hx.2
  have hexp : Real.exp (-1) ≤ Real.exp (-t * x ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold kernel
  calc
    Real.exp (-1) / 2 = Real.exp (-1) * (1 / 2) := by ring
    _ ≤ Real.exp (-t * x ^ 2) * p x :=
      mul_le_mul hexp (hw x hxa) (by norm_num) (Real.exp_nonneg _)

lemma mass_lower {t a : ℝ} (ht : 0 < t) (ha : 0 < a) (hta : t * a ^ 2 = 1)
    {p : ℝ → ℝ} (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1)
    (hw : ∀ x, |x| ≤ a → (1 / 2 : ℝ) ≤ p x) :
    a * Real.exp (-1) / 4 ≤ mass t p := by
  have hi := kernel_integrable ht hm hp
  calc
    a * Real.exp (-1) / 4 = ∫ x in Icc (a / 2) a, Real.exp (-1) / 2 := by
      rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (by linarith), smul_eq_mul]
      ring
    _ ≤ ∫ x in Icc (a / 2) a, kernel t p x := by
      apply integral_mono_ae (integrable_const _) hi.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact kernel_window_lower ht ha hta hw hx
    _ ≤ mass t p := setIntegral_le_integral hi
      (ae_of_all _ fun x ↦ kernel_nonneg (fun y ↦ (hp y).1) x)

lemma mass_pos {t a : ℝ} (ht : 0 < t) (ha : 0 < a) (hta : t * a ^ 2 = 1)
    {p : ℝ → ℝ} (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1)
    (hw : ∀ x, |x| ≤ a → (1 / 2 : ℝ) ≤ p x) : 0 < mass t p :=
  lt_of_lt_of_le (by positivity) (mass_lower ht ha hta hm hp hw)

lemma mass_upper {t : ℝ} (ht : 0 < t) {p : ℝ → ℝ}
    (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1) :
    mass t p ≤ Real.sqrt (Real.pi / t) := by
  rw [← integral_gaussian t]
  apply integral_mono_ae (kernel_integrable ht hm hp) (integrable_exp_neg_mul_sq ht)
  filter_upwards [] with x
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (hp x).2

lemma secondMomentNumerator_lower {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (hta : t * a ^ 2 = 1) {p : ℝ → ℝ}
    (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1)
    (hw : ∀ x, |x| ≤ a → (1 / 2 : ℝ) ≤ p x) :
    a ^ 3 * Real.exp (-1) / 16 ≤ secondMomentNumerator t p := by
  have hi := secondMoment_integrable ht hm hp
  calc
    a ^ 3 * Real.exp (-1) / 16 =
        ∫ x in Icc (a / 2) a, a ^ 2 * Real.exp (-1) / 8 := by
      rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (by linarith), smul_eq_mul]
      ring
    _ ≤ ∫ x in Icc (a / 2) a, x ^ 2 * kernel t p x := by
      apply integral_mono_ae (integrable_const _) hi.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hsq : a ^ 2 / 4 ≤ x ^ 2 := by nlinarith [hx.1]
      have hk := kernel_window_lower ht ha hta hw hx
      calc
        a ^ 2 * Real.exp (-1) / 8 = (a ^ 2 / 4) * (Real.exp (-1) / 2) := by ring
        _ ≤ x ^ 2 * kernel t p x := mul_le_mul hsq hk (by positivity) (sq_nonneg x)
    _ ≤ secondMomentNumerator t p := setIntegral_le_integral hi
      (ae_of_all _ fun x ↦ mul_nonneg (sq_nonneg x) (kernel_nonneg (fun y ↦ (hp y).1) x))

/-- Positive universal constant in the Gaussian-window argument. -/
def windowConstant : ℝ := Real.exp (-1) / (16 * Real.sqrt Real.pi)

lemma windowConstant_pos : 0 < windowConstant := by unfold windowConstant; positivity

/-- Analytic Gaussian-window helper for Corollary 4.10, with fully defined
Lebesgue-integral moments and no probabilistic tail bound taken as an axiom. -/
theorem gaussian_window_secondMoment {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (hta : t * a ^ 2 = 1) {p : ℝ → ℝ}
    (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1)
    (hw : ∀ x, |x| ≤ a → (1 / 2 : ℝ) ≤ p x) :
    windowConstant * a ^ 2 ≤ secondMomentNumerator t p / mass t p := by
  have hmpos := mass_pos ht ha hta hm hp hw
  have hml := mass_upper ht hm hp
  have hnl := secondMomentNumerator_lower ht ha hta hm hp hw
  have hteq : t = 1 / a ^ 2 := by apply (eq_div_iff (ne_of_gt (sq_pos_of_pos ha))).mpr; exact hta
  have hsqrt : Real.sqrt (Real.pi / t) = a * Real.sqrt Real.pi := by
    rw [Real.sqrt_div (le_of_lt Real.pi_pos), hteq, Real.sqrt_div (by norm_num),
      Real.sqrt_one, Real.sqrt_sq_eq_abs, abs_of_pos ha]
    field_simp
  rw [hsqrt] at hml
  apply (le_div_iff₀ hmpos).mpr
  calc
    windowConstant * a ^ 2 * mass t p ≤ windowConstant * a ^ 2 * (a * Real.sqrt Real.pi) :=
      mul_le_mul_of_nonneg_left hml (mul_nonneg (le_of_lt windowConstant_pos) (sq_nonneg a))
    _ = a ^ 3 * Real.exp (-1) / 16 := by
      unfold windowConstant
      field_simp
      <;> ring
    _ ≤ secondMomentNumerator t p := hnl

/-- The normalized axial probability measure, defined by its Lebesgue density. -/
def axialLaw (t : ℝ) (p : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (kernel t p x / mass t p))

lemma axialLaw_probability {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (hta : t * a ^ 2 = 1) {p : ℝ → ℝ}
    (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1)
    (hw : ∀ x, |x| ≤ a → (1 / 2 : ℝ) ≤ p x) :
    IsProbabilityMeasure (axialLaw t p) := by
  have hmpos := mass_pos ht ha hta hm hp hw
  have hi : Integrable (fun x ↦ kernel t p x / mass t p) :=
    (kernel_integrable ht hm hp).div_const _
  have hn : 0 ≤ᵐ[volume] (fun x ↦ kernel t p x / mass t p) :=
    ae_of_all _ fun x ↦ div_nonneg (kernel_nonneg (fun y ↦ (hp y).1) x) hmpos.le
  constructor
  rw [axialLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div]
  change ENNReal.ofReal (mass t p / mass t p) = 1
  rw [div_self (ne_of_gt hmpos), ENNReal.ofReal_one]

lemma integral_axialLaw {t : ℝ} {p : ℝ → ℝ} (hm : Measurable p)
    (hp : ∀ x, 0 ≤ p x) (hmpos : 0 < mass t p) (f : ℝ → ℝ) :
    ∫ x, f x ∂axialLaw t p = (∫ x, kernel t p x * f x) / mass t p := by
  rw [axialLaw, integral_withDensity_eq_integral_toReal_smul
    (by unfold kernel; fun_prop) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (kernel_nonneg hp _) hmpos.le), smul_eq_mul,
    div_mul_eq_mul_div]
  exact integral_div _ _

lemma axialLaw_mean_zero {t : ℝ} {p : ℝ → ℝ} (hm : Measurable p)
    (hp : ∀ x, 0 ≤ p x) (hmpos : 0 < mass t p) (heven : ∀ x, p (-x) = p x) :
    ∫ x, x ∂axialLaw t p = 0 := by
  rw [integral_axialLaw hm hp hmpos]
  have h := integral_neg_eq_self (fun x : ℝ ↦ kernel t p x * x) volume
  have heq : (fun x : ℝ ↦ kernel t p (-x) * (-x)) =
      (fun x : ℝ ↦ -(kernel t p x * x)) := by
    funext x
    simp [kernel, heven x]
  rw [heq, integral_neg] at h
  have hz : (∫ x, kernel t p x * x) = 0 := by linarith
  rw [hz, zero_div]

lemma axialLaw_variance_eq {t : ℝ} {p : ℝ → ℝ} (hm : Measurable p)
    (hp : ∀ x, 0 ≤ p x) (hmpos : 0 < mass t p) (heven : ∀ x, p (-x) = p x) :
    variance (fun x : ℝ ↦ x) (axialLaw t p) = secondMomentNumerator t p / mass t p := by
  rw [variance_eq_integral (X := fun x : ℝ ↦ x) (by fun_prop), axialLaw_mean_zero hm hp hmpos heven]
  simp only [sub_zero]
  rw [integral_axialLaw hm hp hmpos]
  unfold secondMomentNumerator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- Actual variance under the normalized axial density. This proves the
Gaussian-window implication in Corollary 4.10, conditionally only on its natural
measurable acceptance-function hypotheses. -/
theorem gaussian_window_variance {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (hta : t * a ^ 2 = 1) {p : ℝ → ℝ}
    (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1)
    (heven : ∀ x, p (-x) = p x)
    (hw : ∀ x, |x| ≤ a → (1 / 2 : ℝ) ≤ p x) :
    windowConstant / t ≤ variance (fun x : ℝ ↦ x) (axialLaw t p) := by
  rw [axialLaw_variance_eq hm (fun x ↦ (hp x).1) (mass_pos ht ha hta hm hp hw) heven]
  have h := gaussian_window_secondMoment ht ha hta hm hp hw
  have heq : windowConstant / t = windowConstant * a ^ 2 := by
    apply (div_eq_iff (ne_of_gt ht)).mpr
    calc
      windowConstant = windowConstant * (t * a ^ 2) := by rw [hta, mul_one]
      _ = windowConstant * a ^ 2 * t := by ring
  rwa [heq]

/-- The actual tilted-slice density has variance of Gaussian order once the
deterministic scale inequalities hold. This does not assert the still-required
geometric marginal identification or the raw covariance asymptotics. -/
theorem actual_tiltedSlice_variance (d : ℕ) {τ Δ b t a : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) (hΔ : 0 ≤ Δ)
    (ht : 0 < t) (ha : 0 < a) (hta : t * a ^ 2 = 1)
    (hdef : 2 * Δ * (1 + Real.sqrt b * a) + Δ ≤
      (d : ℝ) * LowerProbability.meanDeficitConstant * τ)
    (hrate : (9 / 2 : ℝ) * Real.log 2 ≤ Δ ^ 2 / (d : ℝ)) :
    windowConstant / t ≤ variance (fun x : ℝ ↦ x)
      (axialLaw t (LowerProbability.tiltedSlice d τ Δ b)) := by
  apply gaussian_window_variance ht ha hta
    (LowerProbability.tiltedSlice_measurable d τ Δ b)
    (LowerProbability.tiltedSlice_mem_Icc d τ Δ b)
    (LowerProbability.tiltedSlice_even d τ Δ b)
  intro z hz
  have hdefz : 2 * Δ * (1 + Real.sqrt b * |z|) + Δ ≤
      (d : ℝ) * LowerProbability.meanDeficitConstant * τ := by
    have hm := mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg b)
    have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * Δ by positivity)
    nlinarith
  have hp := LowerProbability.tiltedSlice_acceptance_of_deficit d hτ hΔ hdefz
  have he : Real.exp (-2 * Δ ^ 2 / (9 * (d : ℝ))) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-2 * Δ ^ 2 / (9 * (d : ℝ))) ≤ Real.exp (-Real.log 2) := by
        apply Real.exp_le_exp.mpr
        have hrewrite : -2 * Δ ^ 2 / (9 * (d : ℝ)) = -(2 / 9 : ℝ) * (Δ ^ 2 / (d : ℝ)) := by ring
        rw [hrewrite]
        linarith
      _ = (1 / 2 : ℝ) := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  linarith

end LowerMarginal
end GaussianTilt
