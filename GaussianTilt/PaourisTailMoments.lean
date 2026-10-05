import GaussianTilt.PaourisTruncation

/-! # Real moments from actual shifted exponential tails

The positive part above the deterministic threshold is pushed forward to a
real probability measure. The proved scalar layer-cake estimate and Minkowski
then give genuine integrability, not a bound on a possibly undefined integral.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace GaussianTilt.Paouris

theorem moment_of_shifted_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Measurable g) (hgn : ∀ x, 0 ≤ g x) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 < C)
    (htail : ∀ t : ℝ, 0 < t → μ {x | a + C * t < g x} ≤
      ENNReal.ofReal (6 * Real.exp (-t / 4))) {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun x ↦ g x ^ p) μ ∧
      (∫ x, g x ^ p ∂μ) ^ (1 / p) ≤ a + 48 * C * p := by
  let d : Ω → ℝ := fun x ↦ max 0 ((g x - a) / C)
  have hd : Measurable d := measurable_const.max ((hg.sub_const a).div_const C)
  have hdn (x : Ω) : 0 ≤ d x := le_max_left _ _
  have htaild : ∀ t : ℝ, 0 < t → (μ.map d) {y : ℝ | t < |y|} ≤
      ENNReal.ofReal (6 * Real.exp (-t / 4)) := by
    intro t ht
    rw [Measure.map_apply hd (measurableSet_lt measurable_const measurable_abs)]
    have heq : d ⁻¹' {y : ℝ | t < |y|} = {x | a + C * t < g x} := by
      ext x
      simp only [mem_preimage, mem_setOf_eq, abs_of_nonneg (hdn x), d, lt_max_iff,
        not_lt.mpr ht.le, false_or, lt_div_iff₀ hC]
      constructor <;> intro h <;> nlinarith
    rw [heq]
    exact htail t ht
  obtain ⟨hId, hMd⟩ := ScalarLogConcaveMoments.moment_of_exponential_tail (μ.map d) htaild hp
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpn : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ p by linarith)
  have hφ : Measurable (fun y : ℝ ↦ |y| ^ p) := by fun_prop
  have hId' : Integrable (fun x ↦ d x ^ p) μ := by
    have h := (integrable_map_measure hφ.aestronglyMeasurable hd.aemeasurable).mp hId
    simpa only [Function.comp_def, abs_of_nonneg (hdn _)] using h
  have hdLp : MemLp d (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff hd.aestronglyMeasurable hpne ENNReal.ofReal_ne_top).mp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hdn _), ENNReal.toReal_ofReal hp0.le] using hId'
  have hdBound : eLpNorm d (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (48 * p) := by
    rw [hdLp.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top]
    rw [integral_map hd.aemeasurable hφ.aestronglyMeasurable] at hMd
    simp only [abs_of_nonneg (hdn _)] at hMd
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs, abs_of_nonneg (hdn _),
      one_div] using ENNReal.ofReal_le_ofReal hMd
  have hbound (x : Ω) : g x ≤ a + C * d x := by
    have h := le_max_right 0 ((g x - a) / C)
    change (g x - a) / C ≤ d x at h
    have hh := (div_le_iff₀ hC).mp h
    nlinarith
  have hsum : MemLp (fun x ↦ a + C * d x) (ENNReal.ofReal p) μ :=
    (memLp_const a).add (hdLp.const_mul C)
  have hgLp : MemLp g (ENNReal.ofReal p) μ := hsum.mono' hg.aestronglyMeasurable
    (ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (hgn x)] using hbound x))
  refine ⟨?_, ?_⟩
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (hgn _), ENNReal.toReal_ofReal hp0.le] using
      hgLp.integrable_norm_rpow hpne ENNReal.ofReal_ne_top
  · have hmono : eLpNorm g (ENNReal.ofReal p) μ ≤
        eLpNorm (fun x ↦ a + C * d x) (ENNReal.ofReal p) μ :=
      eLpNorm_mono_ae (ae_of_all _ (fun x ↦ by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hgn x),
          abs_of_nonneg (add_nonneg ha (mul_nonneg hC.le (hdn x)))] using hbound x))
    have htri := eLpNorm_add_le (μ := μ) (f := fun _ ↦ a) (g := C • d)
      aestronglyMeasurable_const (hd.aestronglyMeasurable.const_smul C) hpn
    have hnorm : eLpNorm g (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (a + 48 * C * p) := by
      calc
        _ ≤ eLpNorm (fun x ↦ a + C * d x) (ENNReal.ofReal p) μ := hmono
        _ ≤ eLpNorm (fun _ ↦ a) (ENNReal.ofReal p) μ +
            eLpNorm (C • d) (ENNReal.ofReal p) μ := htri
        _ = ENNReal.ofReal a + ENNReal.ofReal C * eLpNorm d (ENNReal.ofReal p) μ := by
          rw [eLpNorm_const a hpne (NeZero.ne μ), eLpNorm_const_smul]
          simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg ha, abs_of_pos hC]
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal C * ENNReal.ofReal (48 * p) := by gcongr
        _ = _ := by
          rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_add ha (by positivity)]
          congr 1
          ring
    rw [hgLp.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top] at hnorm
    simp only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs, abs_of_nonneg (hgn _)] at hnorm
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ a + 48 * C * p)).mp hnorm
    simpa only [one_div] using h

/-- Any normalized Paouris-type tail yields all real positive moments, with
no integrability assumption. The dimension enters only through `s`. -/
theorem moment_of_scaled_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ}
    (hg : Measurable g) (hgn : ∀ x, 0 ≤ g x) {s C : ℝ} (hs : 0 < s) (hC : 0 < C)
    (htail : ∀ t : ℝ, 1 ≤ t → μ.real {x | C * t * s ≤ g x} ≤ Real.exp (-t * s))
    {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun x ↦ g x ^ p) μ ∧
      (∫ x, g x ^ p ∂μ) ^ (1 / p) ≤ 48 * C * (s + p) := by
  have ht' : ∀ t : ℝ, 0 < t → μ {x | C * s + C * t < g x} ≤
      ENNReal.ofReal (6 * Real.exp (-t / 4)) := by
    intro t ht
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (by positivity)).mpr
    have hτ : 1 ≤ 1 + t / s := le_add_of_nonneg_right (div_nonneg ht.le hs.le)
    have h := htail (1 + t / s) hτ
    have heq : C * (1 + t / s) * s = C * s + C * t := by
      field_simp
    rw [heq] at h
    have hmono : μ.real {x | C * s + C * t < g x} ≤
        μ.real {x | C * s + C * t ≤ g x} :=
      measureReal_mono (fun x hx ↦ (show C * s + C * t < g x from hx).le)
    apply (hmono.trans h).trans
    have he : -(1 + t / s) * s ≤ -t / 4 := by
      rw [neg_mul, add_mul, one_mul, div_mul_cancel₀ t hs.ne']
      linarith
    have hx := Real.exp_le_exp.mpr he
    nlinarith [Real.exp_pos (-t / 4)]
  obtain ⟨hi, hb⟩ := moment_of_shifted_exponential_tail μ hg hgn
    (mul_nonneg hC.le hs.le) hC ht' hp
  refine ⟨hi, hb.trans ?_⟩
  nlinarith [mul_nonneg hC.le hs.le]

/-- Universal constant for the original noncompact norm moment bound. -/
def generalPaourisMomentConstant : ℝ := 48 * generalPaourisTailConstant

lemma generalPaourisMomentConstant_pos : 0 < generalPaourisMomentConstant :=
  mul_pos (by norm_num) generalPaourisTailConstant_pos

theorem isotropic_norm_moment_le (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hl : Reference.logconcave μ) (hi : Reference.isotropic μ) {p : ℝ} (hp : 2 ≤ p) :
    Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ p) μ ∧
      (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤
        generalPaourisMomentConstant * (Real.sqrt (n : ℝ) + p) := by
  by_cases hn : n = 0
  · subst n
    have hz (x : Reference.Space 0) : x = 0 := Subsingleton.elim _ _
    have hp0 : p ≠ 0 := by linarith
    simp only [hz, norm_zero, Real.zero_rpow hp0, integrable_zero, integral_zero,
      Real.zero_rpow (one_div_ne_zero hp0), Nat.cast_zero, Real.sqrt_zero, zero_add, true_and]
    exact mul_nonneg generalPaourisMomentConstant_pos.le (by linarith)
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact moment_of_scaled_tail μ continuous_norm.measurable (fun x ↦ norm_nonneg x)
      (Real.sqrt_pos.mpr hnpos) generalPaourisTailConstant_pos
      (fun t ht ↦ isotropic_norm_tail μ hl hi ht) hp

end GaussianTilt.Paouris
