import GaussianTilt.GaussianConcentration
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Real-order Gaussian Lipschitz moment bounds

The proved centered MGF estimate gives all real moments.  Exponential
optimization gives a universal square-root-of-order bound, and Minkowski's
inequality then restores the mean with coefficient one.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.Paouris
variable {n : ℕ}

lemma standardGaussian_lipschitz_abs_rpow_integrable {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun x ↦ |f x| ^ p) (standardGaussian n) := by
  exact ProbabilityTheory.integrable_rpow_abs_of_integrable_exp_mul
    (t := 1) (by norm_num)
    (standardGaussian_exp_lipschitz_integrable hf 1)
    (standardGaussian_exp_lipschitz_integrable hf (-1)) hp

lemma standardGaussian_center_abs_rpow_integrable {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun x ↦ |f x - ∫ y, f y ∂standardGaussian n| ^ p) (standardGaussian n) := by
  exact ProbabilityTheory.integrable_rpow_abs_of_integrable_exp_mul
    (t := 1) (by norm_num)
    (standardGaussian_exp_center_integrable hf 1)
    (standardGaussian_exp_center_integrable hf (-1)) hp

/-- An explicit exponential optimization estimate for the centered moment. -/
lemma standardGaussian_center_moment_bound_parameter {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {p t : ℝ} (hp : 0 ≤ p) (ht : 0 < t) :
    (∫ x, |f x - ∫ y, f y ∂standardGaussian n| ^ p ∂standardGaussian n) ≤
      (p / t) ^ p * (2 * Real.exp ((t * (Real.pi / 2) * K) ^ 2 / 2)) := by
  have hip := standardGaussian_exp_center_integrable hf t
  have hin := standardGaussian_exp_center_integrable hf (-t)
  calc
    _ ≤ ∫ x, (p / t) ^ p *
        (Real.exp (t * (f x - ∫ y, f y ∂standardGaussian n)) +
          Real.exp (-t * (f x - ∫ y, f y ∂standardGaussian n))) ∂standardGaussian n := by
      apply integral_mono (standardGaussian_center_abs_rpow_integrable hf hp)
        ((hip.add hin).const_mul _)
      intro x
      dsimp only
      exact (ProbabilityTheory.rpow_abs_le_mul_max_exp_of_pos _ hp ht).trans
        (mul_le_mul_of_nonneg_left
          (max_le_add_of_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (by positivity))
    _ = (p / t) ^ p *
        ((∫ x, Real.exp (t * (f x - ∫ y, f y ∂standardGaussian n)) ∂standardGaussian n) +
          ∫ x, Real.exp (-t * (f x - ∫ y, f y ∂standardGaussian n)) ∂standardGaussian n) := by
      rw [integral_const_mul, integral_add hip hin]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have ha := standardGaussian_integral_exp_center_le hf t
      have hb := standardGaussian_integral_exp_center_le hf (-t)
      have he : ((-t) * (Real.pi / 2) * (K : ℝ)) ^ 2 =
          (t * (Real.pi / 2) * K) ^ 2 := by ring
      rw [he] at hb
      linarith

lemma two_mul_exp_half_le_six_rpow {p : ℝ} (hp : 1 ≤ p) :
    2 * Real.exp (p / 2) ≤ (6 : ℝ) ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have htwo : (2 : ℝ) ≤ 2 ^ p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
  have hthree : Real.exp (p / 2) ≤ (3 : ℝ) ^ p := by
    calc
      _ ≤ Real.exp p := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp 1) ^ p := (Real.exp_one_rpow p).symm
      _ ≤ _ := Real.rpow_le_rpow (Real.exp_nonneg _) (by linarith [Real.exp_one_lt_d9]) hp0
  have h := mul_le_mul htwo hthree (Real.exp_nonneg _) (by positivity : (0 : ℝ) ≤ 2 ^ p)
  convert h using 1
  norm_num [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3)]

/-- Centered real-order Gaussian moments are bounded by a universal multiple
of `sqrt p` times the Lipschitz constant. -/
theorem standardGaussian_center_moment_le {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {p : ℝ} (hp : 1 ≤ p) :
    (∫ x, |f x - ∫ y, f y ∂standardGaussian n| ^ p ∂standardGaussian n) ^ (1 / p) ≤
      12 * Real.sqrt p * K := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases hK : K = 0
  · have hconst (x : Reference.Space n) : f x = f 0 := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa only [hK, NNReal.coe_zero, zero_mul] using hf.norm_sub_le x 0)
        (norm_nonneg _)
    simp only [hconst, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
      sub_self, abs_zero, Real.zero_rpow hp0.ne', Real.zero_rpow (by positivity : (1 / p) ≠ 0),
      hK, NNReal.coe_zero, mul_zero, le_refl]
  have hK0 : 0 < (K : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hK)
  let c : ℝ := (Real.pi / 2) * K
  have hc : 0 < c := mul_pos (div_pos Real.pi_pos (by norm_num)) hK0
  let t : ℝ := Real.sqrt p / c
  have ht : 0 < t := div_pos (Real.sqrt_pos.mpr hp0) hc
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hpt : p / t = c * Real.sqrt p := by
    dsimp [t]
    field_simp
    nlinarith [hsq]
  have htc : (t * (Real.pi / 2) * K) ^ 2 = p := by
    change (t * (Real.pi / 2) * (K : ℝ)) ^ 2 = p
    have he : t * (Real.pi / 2) * K = Real.sqrt p := by
      change t * (Real.pi / 2) * (K : ℝ) = Real.sqrt p
      dsimp [t, c]
      field_simp
    rw [he, hsq]
  have hm := standardGaussian_center_moment_bound_parameter hf hp0.le ht
  rw [hpt, htc] at hm
  have hm' : (∫ x, |f x - ∫ y, f y ∂standardGaussian n| ^ p ∂standardGaussian n) ≤
      (6 * c * Real.sqrt p) ^ p := by
    calc
      _ ≤ (c * Real.sqrt p) ^ p * (2 * Real.exp (p / 2)) := hm
      _ ≤ (c * Real.sqrt p) ^ p * (6 : ℝ) ^ p :=
        mul_le_mul_of_nonneg_left (two_mul_exp_half_le_six_rpow hp) (by positivity)
      _ = _ := by
        rw [← Real.mul_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 6)]
        congr 1
        ring
  have hr := Real.rpow_le_rpow (integral_nonneg fun x ↦ by positivity) hm'
    (by positivity : 0 ≤ 1 / p)
  rw [← Real.rpow_mul (by positivity : 0 ≤ 6 * c * Real.sqrt p),
    mul_one_div_cancel hp0.ne', Real.rpow_one] at hr
  apply hr.trans
  dsimp [c]
  have hπ : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
  nlinarith [mul_le_mul_of_nonneg_right hπ (mul_nonneg (Real.sqrt_nonneg p) K.coe_nonneg)]

lemma standardGaussian_lipschitz_memLp {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {p : ℝ} (hp : 0 < p) :
    MemLp f (ENNReal.ofReal p) (standardGaussian n) := by
  apply (integrable_norm_rpow_iff hf.continuous.aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using
    standardGaussian_lipschitz_abs_rpow_integrable hf hp.le

lemma standardGaussian_center_memLp {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {p : ℝ} (hp : 0 < p) :
    MemLp (fun x ↦ f x - ∫ y, f y ∂standardGaussian n)
      (ENNReal.ofReal p) (standardGaussian n) := by
  apply (integrable_norm_rpow_iff (hf.continuous.sub continuous_const).aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top).mp
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using
    standardGaussian_center_abs_rpow_integrable hf hp.le

/-- The requested real-order Gaussian Lipschitz moment theorem, with the
explicit universal numerical constant `12`. It applies directly to norms
and to every other nonnegative globally Lipschitz observable. -/
theorem standardGaussian_lipschitz_moment_le {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (hf0 : ∀ x, 0 ≤ f x)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ x, (f x) ^ p ∂standardGaussian n) ^ (1 / p) ≤
      (∫ x, f x ∂standardGaussian n) + 12 * Real.sqrt p * K := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpn : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  let m : ℝ := ∫ x, f x ∂standardGaussian n
  have hm : 0 ≤ m := integral_nonneg hf0
  let g : Reference.Space n → ℝ := fun x ↦ f x - m
  have hg : AEStronglyMeasurable g (standardGaussian n) :=
    (hf.continuous.sub continuous_const).aestronglyMeasurable
  have hsum : g + (fun _ ↦ m) = f := by ext x; simp [g]
  have h := eLpNorm_add_le (μ := standardGaussian n) (g := fun _ ↦ m) hg aestronglyMeasurable_const hpn
  rw [hsum,
    MemLp.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top
      (standardGaussian_lipschitz_memLp hf hp0),
    MemLp.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top
      (standardGaussian_center_memLp hf hp0),
    eLpNorm_const m hpne (NeZero.ne (standardGaussian n))] at h
  simp only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs, abs_of_nonneg (hf0 _),
    measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs, abs_of_nonneg hm] at h
  rw [← ENNReal.ofReal_add (by positivity) hm,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have hc := standardGaussian_center_moment_le hf hp
  change (∫ x, f x ^ p ∂standardGaussian n) ^ (1 / p) ≤ m + _
  have he : p⁻¹ = 1 / p := by simp
  rw [he] at h
  linarith

end GaussianTilt.Paouris
