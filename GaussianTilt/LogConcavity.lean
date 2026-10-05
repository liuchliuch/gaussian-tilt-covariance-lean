import GaussianTilt.MomentBridge
import GaussianTilt.Geometry

/-! Elementary logconcavity preservation needed by the original tilt path.
These results do not assume or provide Paouris, Prékopa, or Brascamp–Lieb. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace GaussianTilt.Reference

variable {n : ℕ}

lemma logconcaveDensity_mul {f g : Space n → ℝ}
    (hf : logconcaveDensity f) (hg : logconcaveDensity g) :
    logconcaveDensity (fun x ↦ f x * g x) := by
  refine ⟨fun x ↦ mul_nonneg (hf.1 x) (hg.1 x), hf.2.1.mul hg.2.1, ?_⟩
  intro x y a b ha hb hab
  rw [Real.mul_rpow (hf.1 x) (hg.1 x), Real.mul_rpow (hf.1 y) (hg.1 y)]
  calc
    (f x ^ a * g x ^ a) * (f y ^ b * g y ^ b) =
        (f x ^ a * f y ^ b) * (g x ^ a * g y ^ b) := by ring
    _ ≤ f (a • x + b • y) * g (a • x + b • y) :=
      mul_le_mul (hf.2.2 x y a b ha hb hab) (hg.2.2 x y a b ha hb hab)
        (mul_nonneg (Real.rpow_nonneg (hg.1 x) _) (Real.rpow_nonneg (hg.1 y) _)) (hf.1 _)

lemma norm_sq_convex_combination (x y : Space n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
  have hn : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    simpa only [smul_eq_mul] using (convexOn_univ_norm (E := Space n)).2
      (mem_univ x) (mem_univ y) ha hb hab
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (GaussianTilt.square_convex_combination ha hb hab)

lemma gaussian_logconcaveDensity (t c : ℝ) (ht : 0 ≤ t) :
    logconcaveDensity (fun x : Space n ↦ Real.exp (-t * ‖x‖ ^ 2 - c)) := by
  refine ⟨fun x ↦ (Real.exp_pos _).le, by fun_prop, ?_⟩
  intro x y a b ha hb hab
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (norm_sq_convex_combination x y ha hb hab) ht
  have hc : c * (a + b) = c := by rw [hab, mul_one]
  nlinarith


lemma constant_indicator_logconcaveDensity {K : Set (Space n)}
    (hK : Convex ℝ K) (hm : MeasurableSet K) {c : ℝ} (hc : 0 < c) :
    logconcaveDensity (K.indicator (fun _ ↦ c)) := by
  classical
  have hn : ∀ x : Space n, 0 ≤ K.indicator (fun _ ↦ c) x := by
    intro x
    by_cases hx : x ∈ K <;> simp [hx, hc.le]
  refine ⟨hn, measurable_const.indicator hm, ?_⟩
  intro x y a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hp := hK hx hy ha hb hab
      simp only [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hp]
      rw [← Real.rpow_add hc, hab, Real.rpow_one]
    · simpa [hy, Real.zero_rpow hb0] using hn (a • x + b • y)
  · simpa [hx, Real.zero_rpow ha0] using hn (a • x + b • y)

lemma uniform_probability {K : Set (Space n)} (hK : convexBody K) :
    IsProbabilityMeasure (uniform K) := by
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (Measure.measure_pos_of_nonempty_interior volume hK.2.2).ne' hK.2.1.measure_ne_top

lemma uniform_compactlySupported {K : Set (Space n)} (hK : convexBody K) :
    compactlySupported (uniform K) := by
  refine ⟨K, hK.2.1, ?_⟩
  simp [uniform, Measure.restrict_apply, hK.2.1.measurableSet.compl]

lemma uniform_logconcave {K : Set (Space n)} (hK : convexBody K) :
    logconcave (uniform K) := by
  classical
  have hpos : 0 < volume K := Measure.measure_pos_of_nonempty_interior volume hK.2.2
  have hfin : volume K ≠ ∞ := hK.2.1.measure_ne_top
  let c : ℝ := ((volume K).toReal)⁻¹
  have hc : 0 < c := inv_pos.mpr (ENNReal.toReal_pos hpos.ne' hfin)
  refine ⟨K.indicator (fun _ ↦ c), constant_indicator_logconcaveDensity hK.1
    hK.2.1.measurableSet hc, ?_⟩
  have hf : (fun x ↦ ENNReal.ofReal (K.indicator (fun _ ↦ c) x)) =
      K.indicator (fun _ ↦ (volume K)⁻¹) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [indicator_of_mem hx, c, ENNReal.ofReal_inv_of_pos
        (ENNReal.toReal_pos hpos.ne' hfin), ENNReal.ofReal_toReal hfin]
    · simp [hx]
  rw [hf, withDensity_indicator hK.2.1.measurableSet, withDensity_const]
  rfl

end GaussianTilt.Reference

namespace GaussianTilt.CompactProbability

variable {n : ℕ} (P : CompactProbability n)

lemma logconcave_tilt {t : ℝ} (ht : 0 ≤ t) (h : Reference.logconcave P.measure) :
    Reference.logconcave (P.tilt t) := by
  obtain ⟨f, hf, hμ⟩ := h
  have hg : Reference.logconcaveDensity (P.density t) := by
    have hd : P.density t = (fun x ↦ Real.exp (-t * energy x - P.logPartition t)) :=
      funext (P.density_eq_exp t)
    rw [hd]
    exact Reference.gaussian_logconcaveDensity (n := n) t (P.logPartition t) ht
  refine ⟨fun x ↦ f x * P.density t x, Reference.logconcaveDensity_mul hf hg, ?_⟩
  rw [tilt, hμ, ← withDensity_mul volume hf.2.1.ennreal_ofReal hg.2.1.ennreal_ofReal]
  congr 1
  funext x
  exact (ENNReal.ofReal_mul (hf.1 x)).symm

end GaussianTilt.CompactProbability
