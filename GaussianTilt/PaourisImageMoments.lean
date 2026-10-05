import GaussianTilt.PaourisStrongWeak
import GaussianTilt.LogConcaveLinearImages

/-!
# The logconcave linear-image step in Paouris

Actual density transport and the proved small-direction theorem discharge
the geometric hypothesis of the Gaussian strong/weak assembly. Rank-deficient
images are handled by a proved Euclidean unit annihilator.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n q : ℕ}

lemma compact_inner_moment_mono (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hpr : p ≤ r) (a : Reference.Space n) :
    (∫ x, |⟪a, x⟫_ℝ| ^ p ∂μ) ^ (1 / p) ≤
      (∫ x, |⟪a, x⟫_ℝ| ^ r ∂μ) ^ (1 / r) := by
  have hpm := compact_inner_memLp μ hc (ENNReal.ofReal p) a
  have hrm := compact_inner_memLp μ hc (ENNReal.ofReal r) a
  have h := eLpNorm_le_eLpNorm_of_exponent_le (μ := μ)
    (ENNReal.ofReal_le_ofReal hpr) (f := fun x ↦ ⟪a, x⟫_ℝ) (by fun_prop)
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top hpm,
    MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hr).ne'
      ENNReal.ofReal_ne_top hrm] at h
  simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hr.le, Real.norm_eq_abs,
    ← one_div] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- The genuine small-direction bound for every Gaussian matrix image of an
even compact logconcave law, including non-surjective images. -/
theorem matrix_small_direction_of_even_density
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hAC : μ ≪ volume)
    {f : Reference.Space n → ℝ} (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {R : ℝ} (hR : ∀ x, R < ‖x‖ → f x = 0)
    (p : ℝ) [hp : Fact (1 ≤ p)] [NeZero q] (hpq : p ≤ (q : ℝ))
    (W : Reference.Space (n * q)) :
    ∃ t : Reference.Space q, ‖t‖ = 1 ∧ momentNorm μ hc p hAC (gaussianMatrixAction W t) ≤
      500 * ∫ x, ‖gaussianMatrixTransposeAction W x‖ ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp.out
  let L := gaussianMatrixTransposeCLM W
  by_cases hsurj : Function.Surjective L
  · obtain ⟨g, S, hg, hgm, hgS, hmap, hge⟩ :=
      LogConcaveLinearImages.exists_compact_density_map_surjective L.toLinearMap hsurj
        ⟨hf.1, hf.2.2⟩ hf.2.1 hR
    let ν : Measure (Reference.Space q) := μ.map L
    haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
    have hν : ν = volume.withDensity (fun y ↦ ENNReal.ofReal (g y)) := by
      change μ.map L = _
      rw [hμ]
      exact hmap
    have hcν : Reference.compactlySupported ν := LogConcaveLinearImages.compactlySupported_map hc L.toLinearMap
    obtain ⟨_, t, ht, _, htm⟩ := exists_direction_moment_le_500 ν
      ⟨hg.1, hgm, hg.2⟩ (hge heven) hν (NeZero.pos q)
    have hmono := compact_inner_moment_mono ν hcν hp0
      (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q) hpq t
    simp only [Real.rpow_natCast] at hmono
    have hfull := hmono.trans htm
    have hmapp : (∫ y, |⟪t, y⟫_ℝ| ^ p ∂ν) =
        ∫ x, |⟪gaussianMatrixAction W t, x⟫_ℝ| ^ p ∂μ := by
      have hcfn : Continuous (fun y : Reference.Space q ↦ |⟪t, y⟫_ℝ| ^ p) :=
        (Real.continuous_rpow_const hp0.le).comp (continuous_const.inner continuous_id).abs
      rw [show ν = μ.map L from rfl, integral_map L.measurable.aemeasurable hcfn.aestronglyMeasurable]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change |⟪t, L x⟫_ℝ| ^ p = |⟪gaussianMatrixAction W t, x⟫_ℝ| ^ p
      rw [gaussianMatrix_inner_adjoint]
      rfl
    have hmapnorm : (∫ y, ‖y‖ ∂ν) = ∫ x, ‖gaussianMatrixTransposeAction W x‖ ∂μ :=
      integral_map L.measurable.aemeasurable continuous_norm.aestronglyMeasurable
    rw [hmapp, hmapnorm] at hfull
    exact ⟨t, ht, (momentNorm_apply μ hc p hAC _).trans_le hfull⟩
  · obtain ⟨t, ht, hz⟩ := LogConcaveLinearImages.exists_unit_annihilator L.toLinearMap hsurj
    refine ⟨t, ht, ?_⟩
    have hz' (x : Reference.Space n) : ⟪gaussianMatrixAction W t, x⟫_ℝ = 0 := by
      rw [gaussianMatrix_inner_adjoint]
      exact hz x
    rw [momentNorm_apply]
    simp_rw [hz', abs_zero, Real.zero_rpow hp0.ne', integral_zero,
      Real.zero_rpow (one_div_ne_zero hp0.ne')]
    exact mul_nonneg (by norm_num) (integral_nonneg fun x ↦ norm_nonneg _)

/-- Strong and weak moments for an actual even compact logconcave density.
Every analytic and geometric input has now been discharged. -/
theorem compact_even_strong_weak
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hAC : μ ≪ volume)
    {f : Reference.Space n → ℝ} (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {R : ℝ} (hR : ∀ x, R < ‖x‖ → f x = 0)
    {p : ℝ} (hp2 : 2 ≤ p) {L : ℝ≥0}
    (hunit : ∀ a : Reference.Space n, ‖a‖ = 1 →
      (∫ x, |⟪a, x⟫_ℝ| ^ p ∂μ) ^ (1 / p) ≤ L) :
    (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤
      strongWeakConstant * ((∫ x : Reference.Space n, ‖x‖ ∂μ) + (L : ℝ)) := by
  letI : Fact (1 ≤ p) := ⟨by linarith⟩
  let q : ℕ := Nat.ceil p
  have hqpos : 0 < q := Nat.ceil_pos.mpr (by linarith)
  letI : NeZero q := ⟨hqpos.ne'⟩
  have hpq : p ≤ (q : ℝ) := Nat.le_ceil p
  have hq : (q : ℝ) ≤ 2 * p := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ p by linarith)
    change (q : ℝ) < p + 1 at h
    linarith
  have hbound := momentNorm_le_mul_norm μ hc p hAC L.coe_nonneg hunit
  exact strong_moment_le_mean_add_weak (q := q) μ hc p hAC hp2 hq hbound
    (matrix_small_direction_of_even_density μ hc hAC hf heven hμ hR p hpq)

end GaussianTilt.Paouris
