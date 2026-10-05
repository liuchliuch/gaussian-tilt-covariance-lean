import GaussianTilt.PaourisIsotropic

/-!
# Paouris norm tails from the proved moments

This file performs the real-exponent Markov optimization, including small
positive dimensions. The compact even logconcave theorem is an unconditional
consequence of the analytic and density results already proved in this chain.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace GaussianTilt.Paouris

variable {n : ℕ}

/-- Exact exponential Markov conversion at any positive real moment. -/
theorem norm_tail_of_moment_root (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    {p B : ℝ} (hp : 0 < p) (hB : 0 < B)
    (hI : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ p) μ)
    (hroot : (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤ B) :
    μ.real {x | Real.exp 1 * B ≤ ‖x‖} ≤ Real.exp (-p) := by
  have hnonneg : 0 ≤ ∫ x : Reference.Space n, ‖x‖ ^ p ∂μ :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hmoment := Real.rpow_le_rpow (Real.rpow_nonneg hnonneg _) hroot hp.le
  rw [← Real.rpow_mul hnonneg, one_div_mul_cancel hp.ne', Real.rpow_one] at hmoment
  have hthreshold : 0 < (Real.exp 1 * B) ^ p := Real.rpow_pos_of_pos (mul_pos (Real.exp_pos _) hB) _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x : Reference.Space n ↦ Real.rpow_nonneg (norm_nonneg x) p)
    hI ((Real.exp 1 * B) ^ p)
  have hevent : {x : Reference.Space n | (Real.exp 1 * B) ^ p ≤ ‖x‖ ^ p} =
      {x | Real.exp 1 * B ≤ ‖x‖} := by
    ext x
    exact Real.rpow_le_rpow_iff (mul_nonneg (Real.exp_nonneg _) hB.le) (norm_nonneg x) hp
  rw [hevent] at hmarkov
  have hscale : (Real.exp 1 * B) ^ p * Real.exp (-p) = B ^ p := by
    rw [Real.mul_rpow (Real.exp_nonneg _) hB.le, ← Real.exp_mul, one_mul]
    calc
      Real.exp p * B ^ p * Real.exp (-p) = (Real.exp p * Real.exp (-p)) * B ^ p := by ring
      _ = B ^ p := by rw [← Real.exp_add]; simp
  have h := hmarkov.trans hmoment
  rw [← hscale] at h
  exact (mul_le_mul_left hthreshold).mp h

/-- Real positive moments at `sqrt n + p` imply the normalized Paouris
exponential tail, with an explicit universal rescaling. -/
theorem norm_tail_of_all_positive_moments
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    {C : ℝ} (hC : 0 < C)
    (hmom : ∀ p : ℝ, 2 ≤ p → Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ p) μ ∧
      (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤ C * (Real.sqrt (n : ℝ) + p))
    {t : ℝ} (ht : 1 ≤ t) :
    μ.real {x | (3 * Real.exp 1 * C) * t * Real.sqrt (n : ℝ) ≤ ‖x‖} ≤
      Real.exp (-t * Real.sqrt (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero]
    have hevent : {x : Reference.Space 0 | (0 : ℝ) ≤ ‖x‖} = univ := by
      ext x
      simp only [mem_setOf_eq, mem_univ, iff_true, norm_nonneg]
    rw [hevent, measureReal_univ_eq_one]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn1
    let r : ℝ := t * Real.sqrt (n : ℝ)
    have hr1 : 1 ≤ r := by
      dsimp [r]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hsqrt)]
    have hr : 0 < r := by linarith
    have hpr : 2 ≤ 2 * r := by linarith
    obtain ⟨hI, hM⟩ := hmom (2 * r) hpr
    have hsqr : Real.sqrt (n : ℝ) ≤ r := by
      dsimp [r]
      exact le_mul_of_one_le_left (Real.sqrt_nonneg _) ht
    have hroot : (∫ x : Reference.Space n, ‖x‖ ^ (2 * r) ∂μ) ^ (1 / (2 * r)) ≤ 3 * C * r := by
      have h := mul_le_mul_of_nonneg_left (show Real.sqrt (n : ℝ) + 2 * r ≤ 3 * r by linarith) hC.le
      nlinarith
    have htail := norm_tail_of_moment_root μ (show 0 < 2 * r by positivity)
      (show 0 < 3 * C * r by positivity) hI hroot
    have hthreshold : Real.exp 1 * (3 * C * r) = (3 * Real.exp 1 * C) * t * Real.sqrt (n : ℝ) := by
      dsimp [r]
      ring
    rw [hthreshold] at htail
    apply htail.trans
    apply Real.exp_le_exp.mpr
    have heq : -t * Real.sqrt (n : ℝ) = -r := by dsimp [r]; ring
    rw [heq]
    linarith

/-- Explicit universal threshold factor for the proved compact even case. -/
def compactPaourisTailConstant : ℝ := 3 * Real.exp 1 * compactPaourisMomentConstant

lemma compactPaourisTailConstant_pos : 0 < compactPaourisTailConstant := by
  unfold compactPaourisTailConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) compactPaourisMomentConstant_pos

/-- Paouris's norm tail for actual compact even isotropic logconcave laws.
The general nonsymmetric/noncompact extensions are separate obligations. -/
theorem compact_even_isotropic_norm_tail
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hi : Reference.isotropic μ)
    {f : Reference.Space n → ℝ} (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {R : ℝ} (hR : ∀ x, R < ‖x‖ → f x = 0)
    {t : ℝ} (ht : 1 ≤ t) :
    μ.real {x | compactPaourisTailConstant * t * Real.sqrt (n : ℝ) ≤ ‖x‖} ≤
      Real.exp (-t * Real.sqrt (n : ℝ)) := by
  apply norm_tail_of_all_positive_moments μ compactPaourisMomentConstant_pos _ ht
  intro p hp
  have hI := compact_continuous_integrable μ hc
    ((Real.continuous_rpow_const (show 0 ≤ p by linarith)).comp continuous_norm)
  exact ⟨hI, compact_even_isotropic_moment_le μ hc hi hf heven hμ hR hp⟩

end GaussianTilt.Paouris
