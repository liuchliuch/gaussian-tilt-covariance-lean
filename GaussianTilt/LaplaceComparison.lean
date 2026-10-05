import GaussianTilt.GaussianSmoothing
import GaussianTilt.LaplaceCutoff
import Mathlib.MeasureTheory.Integral.Layercake

/-! # Transfer from CDF distance to the one-sided Laplace transform -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology
namespace GaussianTilt.LaplaceComparison
open GaussianSmoothing LaplaceCutoff

lemma probability_Icc_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) :
    μ.real (Set.Icc a b) = cdf μ b - Function.leftLim (cdf μ) a := by
  have h : μ (Set.Icc a b) = ENNReal.ofReal (cdf μ b - Function.leftLim (cdf μ) a) :=
    (congrArg (fun m : Measure ℝ ↦ m (Set.Icc a b)) (measure_cdf μ)).symm.trans
      ((cdf μ).measure_Icc a b)
  rw [measureReal_def, h, ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr ((monotone_cdf μ).leftLim_le hab)

lemma leftLim_cdf_comparison {μ ν : Measure ℝ} {D : ℝ}
    (hD : ∀ a, |cdf μ a - cdf ν a| ≤ D) (a : ℝ) :
    |Function.leftLim (cdf μ) a - Function.leftLim (cdf ν) a| ≤ D := by
  have hl := ((monotone_cdf μ).tendsto_leftLim a).sub ((monotone_cdf ν).tendsto_leftLim a)
  exact le_of_tendsto hl.abs (Eventually.of_forall hD)

/-- Kolmogorov distance controls closed intervals as well, including atoms. -/
lemma interval_cdf_comparison {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {D : ℝ} (hD : ∀ a, |cdf μ a - cdf ν a| ≤ D) (a b : ℝ) :
    |μ.real (Set.Icc a b) - ν.real (Set.Icc a b)| ≤ 2 * D := by
  by_cases hab : a ≤ b
  · rw [probability_Icc_eq_cdf μ hab, probability_Icc_eq_cdf ν hab]
    have hx := abs_le.mp (hD b)
    have hy := abs_le.mp (leftLim_cdf_comparison hD a)
    apply abs_le.mpr
    constructor <;> linarith
  · have hnonneg : 0 ≤ D := (abs_nonneg _).trans (hD 0)
    simp [Set.Icc_eq_empty hab]
    linarith

/-- The bounded measurable one-sided exponential kernel. -/
def laplaceKernel (t : ℝ) : ℝ → ℝ :=
  (Set.Ici 0).indicator (fun x ↦ Real.exp (-t * x))

lemma laplaceKernel_measurable (t : ℝ) : Measurable (laplaceKernel t) :=
  (show Measurable (fun x : ℝ ↦ Real.exp (-t * x)) by fun_prop).indicator measurableSet_Ici

lemma laplaceKernel_nonneg (t x : ℝ) : 0 ≤ laplaceKernel t x :=
  Set.indicator_nonneg (fun _ _ ↦ Real.exp_nonneg _) _

lemma laplaceKernel_le_one {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : laplaceKernel t x ≤ 1 := by
  by_cases hx : 0 ≤ x
  · rw [laplaceKernel, Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  · rw [laplaceKernel, Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx)]
    norm_num

lemma laplaceKernel_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) : Integrable (laplaceKernel t) μ := by
  apply Integrable.of_bound (laplaceKernel_measurable t).aestronglyMeasurable 1
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (laplaceKernel_nonneg t x)]
    exact laplaceKernel_le_one ht x

lemma laplaceKernel_superlevel {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    {x : ℝ | u ≤ laplaceKernel t x} = Set.Icc 0 (-Real.log u / t) := by
  ext x
  by_cases hx : 0 ≤ x
  · rw [Set.mem_setOf_eq, laplaceKernel,
      Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx),
      ← Real.log_le_iff_le_exp hu]
    simp only [Set.mem_Icc, hx, true_and]
    rw [le_div_iff₀ ht]
    constructor <;> intro h <;> nlinarith
  · simp only [Set.mem_setOf_eq, Set.mem_Icc, hx, false_and]
    rw [laplaceKernel, Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx)]
    exact iff_false_intro (not_le.mpr hu)

lemma laplaceLevel_measurable (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Measurable (fun u : ℝ ↦ μ.real {x | u ≤ laplaceKernel t x}) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ≤ laplaceKernel t p.2} :=
    measurableSet_le measurable_fst ((laplaceKernel_measurable t).comp measurable_snd)
  exact (measurable_measure_prodMk_left (ν := μ) hs).ennreal_toReal

lemma laplaceLevel_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    IntegrableOn (fun u : ℝ ↦ μ.real {x | u ≤ laplaceKernel t x}) (Set.Ioc (0 : ℝ) 1) := by
  apply Integrable.of_bound (laplaceLevel_measurable μ t).aestronglyMeasurable.restrict 1
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

/-- A uniform CDF approximation transfers to a one-sided Laplace approximation
with no loss depending on the Laplace parameter. Layer-cake integration proves
this directly, including possible atoms at the origin. -/
theorem oneSidedLaplace_cdf_bound {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {D t : ℝ}
    (hD : ∀ a, |cdf μ a - cdf ν a| ≤ D) (ht : 0 < t) :
    |oneSidedLaplace μ t - oneSidedLaplace ν t| ≤ 2 * D := by
  have heq (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
      oneSidedLaplace ρ t = ∫ u in Set.Ioc (0 : ℝ) 1,
        ρ.real {x | u ≤ laplaceKernel t x} := by
    rw [oneSidedLaplace, ← integral_indicator measurableSet_Ici]
    exact (laplaceKernel_integrable ρ ht.le).integral_eq_integral_Ioc_meas_le
      (ae_of_all _ (laplaceKernel_nonneg t)) (ae_of_all _ (laplaceKernel_le_one ht.le))
  rw [heq μ, heq ν, ← integral_sub (laplaceLevel_integrable μ t) (laplaceLevel_integrable ν t),
    ← Real.norm_eq_abs]
  have hb : ∀ᵐ u ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ‖μ.real {x | u ≤ laplaceKernel t x} - ν.real {x | u ≤ laplaceKernel t x}‖ ≤ 2 * D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [laplaceKernel_superlevel ht hu.1, Real.norm_eq_abs]
    exact interval_cdf_comparison hD _ _
  have h := norm_integral_le_of_norm_le_const hb
  simpa only [measureReal_restrict_apply_univ, Real.volume_real_Ioc,
    sub_zero, max_eq_left zero_le_one, mul_one] using h

lemma oneSidedLaplace_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    oneSidedLaplace μ 0 = 1 - Function.leftLim (cdf μ) 0 := by
  have h : μ (Set.Ici 0) = ENNReal.ofReal (1 - Function.leftLim (cdf μ) 0) :=
    (congrArg (fun m : Measure ℝ ↦ m (Set.Ici 0)) (measure_cdf μ)).symm.trans
      ((cdf μ).measure_Ici (tendsto_cdf_atTop μ) 0)
  simp only [oneSidedLaplace, neg_zero, zero_mul, Real.exp_zero, setIntegral_const, smul_eq_mul, mul_one]
  rw [measureReal_def, h, ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (((monotone_cdf μ).leftLim_le le_rfl).trans (cdf_le_one μ 0))

lemma oneSidedLaplace_cdf_bound_nonneg {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {D t : ℝ}
    (hD : ∀ a, |cdf μ a - cdf ν a| ≤ D) (ht : 0 ≤ t) :
    |oneSidedLaplace μ t - oneSidedLaplace ν t| ≤ 2 * D := by
  rcases ht.eq_or_lt with hzero | hpos
  · rw [← hzero, oneSidedLaplace_zero, oneSidedLaplace_zero]
    have h := leftLim_cdf_comparison hD 0
    have hnonneg := (abs_nonneg _).trans h
    have he : (1 - Function.leftLim (cdf μ) 0) - (1 - Function.leftLim (cdf ν) 0) =
        -(Function.leftLim (cdf μ) 0 - Function.leftLim (cdf ν) 0) := by ring
    rw [he, abs_neg]
    linarith
  · exact oneSidedLaplace_cdf_bound hD hpos

lemma oneSidedLaplace_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : oneSidedLaplace μ t ≤ oneSidedLaplace μ s := by
  rw [oneSidedLaplace, oneSidedLaplace, ← integral_indicator measurableSet_Ici,
    ← integral_indicator measurableSet_Ici]
  apply integral_mono (laplaceKernel_integrable μ (hs.trans hst)) (laplaceKernel_integrable μ hs)
  intro x
  by_cases hx : 0 ≤ x
  · simp only [laplaceKernel, Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · simp [laplaceKernel, Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx)]

lemma exp_lipschitz_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Iic (0 : ℝ)) (𝕜 := ℝ) (f := Real.exp) (fun x _ ↦ Real.differentiable_exp x)
    (C := 1) (fun x hx ↦ by simpa using Real.exp_le_one_iff.mpr hx)
    (convex_Iic 0) (x := b) (y := a) hb ha
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- The Laplace kernel is Lipschitz in its nonnegative parameter, with an
actual first-moment constant. -/
theorem oneSidedLaplace_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hfirst : Integrable (fun x : ℝ ↦ |x|) μ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |oneSidedLaplace μ s - oneSidedLaplace μ t| ≤ |s - t| * ∫ x, |x| ∂μ := by
  have hp (x : ℝ) : ‖laplaceKernel s x - laplaceKernel t x‖ ≤ |s - t| * |x| := by
    rw [Real.norm_eq_abs]
    by_cases hx : 0 ≤ x
    · rw [laplaceKernel, laplaceKernel, Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx),
        Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
      have h := exp_lipschitz_nonpos (a := -s * x) (b := -t * x)
        (by nlinarith) (by nlinarith)
      have he : -s * x - -t * x = -(s - t) * x := by ring
      rwa [he, abs_mul, abs_neg] at h
    · simp only [laplaceKernel, Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx),
        sub_self, abs_zero]
      positivity
  have hdiff := (laplaceKernel_integrable μ hs).sub (laplaceKernel_integrable μ ht)
  have hb := (norm_integral_le_integral_norm (fun x ↦ laplaceKernel s x - laplaceKernel t x)).trans
    (integral_mono hdiff.norm (hfirst.const_mul |s - t|) hp)
  rw [integral_sub (laplaceKernel_integrable μ hs) (laplaceKernel_integrable μ ht),
    integral_const_mul, Real.norm_eq_abs] at hb
  simpa only [laplaceKernel, integral_indicator measurableSet_Ici, oneSidedLaplace] using hb

/-- A universal positive lower bound for the standard normal Laplace factor,
valid down to parameter zero. -/
theorem gaussian_laplace_lower {t : ℝ} (ht : 0 ≤ t) :
    (Real.exp (-4) / Real.sqrt (2 * Real.pi)) / (1 + t) ≤
      oneSidedLaplace (gaussianReal 0 1) t := by
  have hA : 0 ≤ Real.exp (-4) / Real.sqrt (2 * Real.pi) := by positivity
  by_cases hsmall : t ≤ 1
  · have hcut := gaussian_cutoff_lower (v := 1) (t := 1) (by norm_num) (by norm_num)
    have hsand := (oneSidedLaplace_sandwich (gaussianReal 0 1) (t := 1) (by norm_num)).1
    have hbase : Real.exp (-4) / Real.sqrt (2 * Real.pi) ≤ oneSidedLaplace (gaussianReal 0 1) 1 := by
      simpa using hcut.trans hsand
    exact (div_le_self hA (by linarith)).trans
      (hbase.trans (oneSidedLaplace_antitone _ ht hsmall))
  · have htpos : 0 < t := by linarith
    have hcut := gaussian_cutoff_lower (v := 1) htpos (by
      change 1 ≤ (1 : ℝ) * t ^ 2
      nlinarith [not_le.mp hsmall])
    have hsand := (oneSidedLaplace_sandwich (gaussianReal 0 1) htpos).1
    have hbase : (Real.exp (-4) / Real.sqrt (2 * Real.pi)) / t ≤ oneSidedLaplace (gaussianReal 0 1) t := by
      convert hcut.trans hsand using 1
      simp only [NNReal.coe_one, mul_one]
      ring
    exact (div_le_div_of_nonneg_left hA htpos (by linarith)).trans hbase

end GaussianTilt.LaplaceComparison
