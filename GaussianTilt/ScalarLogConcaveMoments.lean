import GaussianTilt.LogConcaveMarginal
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Real moments of compact even logconcave laws on the line

This file derives scalar weak-moment bounds from actual density logconcavity,
normalization and the second moment. No scalar moment inequality is assumed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.ScalarLogConcaveMoments
open LogConcaveMarginal

lemma logconcave_indicator {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {f : E → ℝ} (hf : IsLogConcave f) {S : Set E} (hS : Convex ℝ S) :
    IsLogConcave (S.indicator f) := by
  classical
  refine ⟨fun x ↦ indicator_nonneg (fun x _ ↦ hf.1 x) x, ?_⟩
  intro x y a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [ha1, hb0]
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · simpa only [indicator_of_mem hx, indicator_of_mem hy,
        indicator_of_mem (hS hx hy ha hb hab)] using hf.2 x y a b ha hb hab
    · rw [indicator_of_notMem hy, Real.zero_rpow hb0, mul_zero]
      exact indicator_nonneg (fun x _ ↦ hf.1 x) _
  · rw [indicator_of_notMem hx, Real.zero_rpow ha0, zero_mul]
    exact indicator_nonneg (fun x _ ↦ hf.1 x) _

/-- The actual one-sided survival integral. -/
def tail (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in Ioi t, f x

lemma tail_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (t : ℝ) : 0 ≤ tail f t :=
  integral_nonneg hf

lemma tail_antitone {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (hi : Integrable f) :
    Antitone (tail f) := by
  intro x y hxy
  exact setIntegral_mono_set hi.integrableOn (Eventually.of_forall hf) (Eventually.of_forall (Ioi_subset_Ioi hxy))

/-- Prékopa applied to the density restricted to a moving half-line. -/
theorem tail_logconcave {f : ℝ → ℝ} (hf : IsLogConcave f) (hm : Measurable f)
    (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0) : IsLogConcave (tail f) := by
  let S : Set (ℝ × ℝ) := {z | z.1 < z.2}
  let F : ℝ × ℝ → ℝ := S.indicator (fun z ↦ f z.2)
  have hS : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    change a * x.1 + b * y.1 < a * x.2 + b * y.2
    change x.1 < x.2 at hx
    change y.1 < y.2 at hy
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hy
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx hap)
        (mul_le_mul_of_nonneg_left hy.le hb)
  have hF : IsLogConcave F := logconcave_indicator
    ⟨fun z ↦ hf.1 z.2, fun x y a b ha hb hab ↦ hf.2 x.2 y.2 a b ha hb hab⟩ hS
  have heq (t : ℝ) : (fun u ↦ F (t, u)) = (Ioi t).indicator f := by
    ext u
    rfl
  have hFm (t : ℝ) : Measurable (fun u ↦ F (t, u)) := by
    rw [heq]
    exact hm.indicator measurableSet_Ioi
  have hFs (t : ℝ) : ∃ A B : ℝ, ∀ u ∉ Icc A B, F (t, u) = 0 := by
    obtain ⟨A, B, hAB⟩ := hs
    refine ⟨A, B, fun u hu ↦ ?_⟩
    change (Ioi t).indicator f u = 0
    by_cases hu' : u ∈ Ioi t <;> simp [hu', hAB u hu]
  have h := marginal_logconcave_of_measurable_compact_slices hF hFm hFs
  have he (t : ℝ) : (∫ u, F (t, u)) = tail f t := by
    rw [heq, integral_indicator measurableSet_Ioi]
    rfl
  simpa only [he] using h

lemma tail_zero_eq_half {f : ℝ → ℝ} (hi : Integrable f)
    (he : ∀ x, f (-x) = f x) (hmass : ∫ x, f x = 1) : tail f 0 = 1 / 2 := by
  have hn : (∫ x in Iic (0 : ℝ), f x) = tail f 0 := by
    have h := integral_comp_neg_Ioi 0 f
    simpa only [he, neg_zero, tail] using h.symm
  have h := intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn (b := 0)
  rw [hn, hmass] at h
  change tail f 0 + tail f 0 = 1 at h
  linarith

lemma integrable_continuous_mul {f g : ℝ → ℝ} (hi : Integrable f)
    (hg : Continuous g) (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0) :
    Integrable (fun x ↦ g x * f x) := by
  obtain ⟨A, B, hAB⟩ := hs
  have h := IntegrableOn.continuousOn_mul hg.continuousOn (hi.integrableOn (s := Icc A B)) isCompact_Icc
  exact h.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by simp [hAB x hx])

lemma tail_four_le {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (hi : Integrable f)
    (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0)
    (hv : ∫ x, x ^ 2 * f x = 1) : tail f 4 ≤ 1 / 16 := by
  have his := integrable_continuous_mul hi (show Continuous (fun x : ℝ ↦ x ^ 2) by fun_prop) hs
  have h : (∫ x, 16 * (Ioi (4 : ℝ)).indicator f x) ≤ ∫ x, x ^ 2 * f x := by
    apply integral_mono ((hi.indicator measurableSet_Ioi).const_mul 16) his
    intro x
    dsimp only
    by_cases hx : x ∈ Ioi (4 : ℝ)
    · rw [indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (by change 4 < x at hx; nlinarith) (hf x)
    · rw [indicator_of_notMem hx, mul_zero]
      exact mul_nonneg (sq_nonneg x) (hf x)
  rw [integral_const_mul, integral_indicator measurableSet_Ioi, hv] at h
  change 16 * tail f 4 ≤ 1 at h
  linarith

lemma log_one_sixteen_le : Real.log (1 / 16 : ℝ) ≤ Real.log (1 / 2 : ℝ) - 1 := by
  apply Real.exp_le_exp.mp
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 16), Real.exp_sub,
    Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
  apply (le_div_iff₀ (Real.exp_pos 1)).mpr
  linarith [Real.exp_one_lt_d9]

lemma logconcave_tail_exponential_bound {T : ℝ → ℝ} (hT : IsLogConcave T)
    (hanti : Antitone T) (hzero : T 0 = 1 / 2) (hfour : T 4 ≤ 1 / 16)
    {t : ℝ} (ht : 0 ≤ t) : T t ≤ 3 * Real.exp (-t / 4) := by
  by_cases ht4 : t ≤ 4
  · have hsmall : T t ≤ 1 / 2 := by simpa only [hzero] using hanti ht
    have hexp : Real.exp (-1) ≤ Real.exp (-t / 4) := Real.exp_le_exp.mpr (by linarith)
    have hnum : (1 : ℝ) ≤ 3 * Real.exp (-1) := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact (le_div_iff₀ (Real.exp_pos 1)).mpr (by linarith [Real.exp_one_lt_d9])
    linarith
  have htp : 0 < t := by linarith
  by_cases hTt : T t = 0
  · rw [hTt]
    positivity
  have hTtp : 0 < T t := lt_of_le_of_ne (hT.1 t) (Ne.symm hTt)
  have hb : 0 ≤ 4 / t := by positivity
  have ha : 0 ≤ 1 - 4 / t := by
    apply sub_nonneg.mpr
    exact (div_le_one htp).mpr (le_of_not_ge ht4)
  have hmajor := hT.2 0 t (1 - 4 / t) (4 / t) ha hb (by ring)
  have hpnt : (1 - 4 / t) • (0 : ℝ) + (4 / t) • t = 4 := by
    simp only [smul_eq_mul, mul_zero, zero_add]
    field_simp
  rw [hpnt, hzero] at hmajor
  have hl := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) _)
      (Real.rpow_pos_of_pos hTtp _)) (hmajor.trans hfour)
  rw [Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) _).ne'
    (Real.rpow_pos_of_pos hTtp _).ne', Real.log_rpow (by norm_num : (0 : ℝ) < 1 / 2),
    Real.log_rpow hTtp] at hl
  have hloghalf : Real.log (1 / 2 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  have hlog : Real.log (T t) ≤ -t / 4 := by
    have h := mul_le_mul_of_nonneg_right
      (hl.trans log_one_sixteen_le) htp.le
    field_simp at h
    nlinarith
  calc
    T t = Real.exp (Real.log (T t)) := (Real.exp_log hTtp).symm
    _ ≤ Real.exp (-t / 4) := Real.exp_le_exp.mpr hlog
    _ ≤ 3 * Real.exp (-t / 4) := by linarith [Real.exp_pos (-t / 4)]

/-- A universal exponential one-sided tail bound derived from the density. -/
theorem tail_le_exp {f : ℝ → ℝ} (hf : IsLogConcave f) (hm : Measurable f)
    (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0)
    (he : ∀ x, f (-x) = f x) (hmass : ∫ x, f x = 1)
    (hv : ∫ x, x ^ 2 * f x = 1) {t : ℝ} (ht : 0 ≤ t) :
    tail f t ≤ 3 * Real.exp (-t / 4) := by
  have hi := integrable_of_compact_support hf hm hs
  exact logconcave_tail_exponential_bound (tail_logconcave hf hm hs)
    (tail_antitone hf.1 hi) (tail_zero_eq_half hi he hmass)
    (tail_four_le hf.1 hi hs hv) ht

end GaussianTilt.ScalarLogConcaveMoments
