import GaussianTilt.LowerFubini
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Quantitative slice integration

This file proves the real-variable integration step in Lemma 4.6. Its envelope
hypotheses are explicit and are not claimed for the cube before the local
moderate-deviation comparison has been established.
-/
noncomputable section
open MeasureTheory Set Filter Real
open scoped Topology

namespace GaussianTilt
namespace SliceMoments

/-- Actual half-line slice moment. -/
def moment (n : ℕ) (p : ℝ → ℝ) : ℝ := ∫ s in Ici (0 : ℝ), s ^ n * p s

lemma polynomial_exp_integrable (n : ℕ) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun s : ℝ ↦ s ^ n * Real.exp (-k * s)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)) (by norm_num) hk)

lemma polynomial_exp_integral (n : ℕ) {k : ℝ} (hk : 0 < k) :
    (∫ s in Ici (0 : ℝ), s ^ n * Real.exp (-k * s)) = (n.factorial : ℝ) / k ^ (n + 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (by positivity) hk
  rw [Real.Gamma_nat_eq_factorial] at h
  simp only [add_sub_cancel_right, Real.rpow_natCast, neg_mul] at h
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  calc
    _ = (1 / k) ^ (n + 1) * (n.factorial : ℝ) := by simpa only [neg_mul] using h
    _ = _ := by rw [div_pow, one_pow]; ring

lemma polynomial_interval_integral (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ s in Icc (0 : ℝ) (1 / r), s ^ n) = 1 / ((n + 1 : ℝ) * r ^ (n + 1)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity), integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, div_pow, one_pow]
  field_simp
  <;> ring

/-- Integrating the local core gives its correct power of the deviation rate. -/
theorem moment_lower {n : ℕ} {p : ℝ → ℝ} {r m c : ℝ} (hr : 0 < r)
    (hpi : IntegrableOn (fun s ↦ s ^ n * p s) (Ici (0 : ℝ)))
    (hp : ∀ s, 0 ≤ s → 0 ≤ p s)
    (hlower : ∀ s ∈ Icc (0 : ℝ) (1 / r), c * m ≤ p s) :
    c * m / ((n + 1 : ℝ) * r ^ (n + 1)) ≤ moment n p := by
  calc
    _ = ∫ s in Icc (0 : ℝ) (1 / r), s ^ n * (c * m) := by
      rw [integral_mul_const, polynomial_interval_integral n hr]
      ring
    _ ≤ ∫ s in Icc (0 : ℝ) (1 / r), s ^ n * p s := by
      apply integral_mono_ae
        ((ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)))
        (hpi.mono_set (by intro s hs; exact hs.1))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact mul_le_mul_of_nonneg_left (hlower s hs) (pow_nonneg hs.1 _)
    _ ≤ moment n p := by
      apply setIntegral_mono_set hpi
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
        exact mul_nonneg (pow_nonneg hs _) (hp s hs)
      · exact ae_of_all _ (by intro s hs; exact hs.1)

/-- Integrating a proved exponential envelope yields the matching upper power. -/
theorem moment_upper {n : ℕ} {p : ℝ → ℝ} {r k m C : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hpi : IntegrableOn (fun s ↦ s ^ n * p s) (Ici (0 : ℝ)))
    (hupper : ∀ s, 0 ≤ s → p s ≤ C * m * Real.exp (-k * r * s)) :
    moment n p ≤ C * m * (n.factorial : ℝ) / (k * r) ^ (n + 1) := by
  calc
    moment n p ≤ ∫ s in Ici (0 : ℝ), (C * m) * (s ^ n * Real.exp (-(k * r) * s)) := by
      apply integral_mono_ae hpi ((polynomial_exp_integrable n (mul_pos hk hr)).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
      have h := mul_le_mul_of_nonneg_left (hupper s hs) (pow_nonneg hs n)
      calc
        _ ≤ s ^ n * (C * m * Real.exp (-k * r * s)) := h
        _ = _ := by rw [show -(k * r) * s = -k * r * s by ring]; ring
    _ = _ := by
      rw [integral_const_mul, polynomial_exp_integral n (mul_pos hk hr)]
      ring

/-- A local exponential comparison and the global Gaussian tail imply a single
exponential envelope. The one numeric compatibility condition precisely records
the tail gap; no tail integral estimate is assumed. -/
theorem global_envelope_of_local_and_gaussian {p : ℝ → ℝ} {r s₀ k c C m : ℝ}
    (hr : 0 ≤ r) (hs₀ : 0 ≤ s₀) (hk : 0 ≤ k) (hc : 0 ≤ c) (hck : c ≤ k)
    (hlocal : ∀ s ∈ Icc (0 : ℝ) s₀, p s ≤ C * m * Real.exp (-c * r * s))
    (hglobal : ∀ s, 0 ≤ s → p s ≤ Real.exp (-k * r * (1 + s) ^ 2))
    (hgap : Real.exp (-r * (k * (1 + s₀) ^ 2 - c * s₀)) ≤ C * m) :
    ∀ s, 0 ≤ s → p s ≤ C * m * Real.exp (-c * r * s) := by
  intro s hs
  by_cases hss : s ≤ s₀
  · exact hlocal s ⟨hs, hss⟩
  · have hss' : s₀ ≤ s := le_of_lt (not_le.mp hss)
    have hpoly : k * (1 + s₀) ^ 2 - c * s₀ ≤ k * (1 + s) ^ 2 - c * s := by
      have hsq : 0 ≤ (s - s₀) * (s + s₀) :=
        mul_nonneg (sub_nonneg.mpr hss') (by linarith)
      have hkdiff : 0 ≤ (k - c) * (s - s₀) :=
        mul_nonneg (sub_nonneg.mpr hck) (sub_nonneg.mpr hss')
      have hksq : 0 ≤ k * ((s - s₀) * (s + s₀)) := mul_nonneg hk hsq
      nlinarith
    calc
      p s ≤ Real.exp (-k * r * (1 + s) ^ 2) := hglobal s hs
      _ ≤ Real.exp (-r * (k * (1 + s₀) ^ 2 - c * s₀)) * Real.exp (-c * r * s) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hpoly hr]
      _ ≤ _ := mul_le_mul_of_nonneg_right hgap (Real.exp_nonneg _)

/-- The local lower exponential comparison is uniformly positive on one
reciprocal-rate window. -/
lemma core_lower_of_local_exponential {p : ℝ → ℝ} {r s₀ c C m : ℝ}
    (hr : 0 < r) (hwindow : 1 / r ≤ s₀) (hC : 0 ≤ C) (hcm : 0 ≤ c * m)
    (hlocal : ∀ s ∈ Icc (0 : ℝ) s₀, c * m * Real.exp (-C * r * s) ≤ p s) :
    ∀ s ∈ Icc (0 : ℝ) (1 / r), (c * Real.exp (-C)) * m ≤ p s := by
  intro s hs
  have hrs : r * s ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hs.2 hr.le
    field_simp at h
    nlinarith
  have he : Real.exp (-C) ≤ Real.exp (-C * r * s) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    (c * Real.exp (-C)) * m = c * m * Real.exp (-C) := by ring
    _ ≤ c * m * Real.exp (-C * r * s) := mul_le_mul_of_nonneg_left he hcm
    _ ≤ p s := hlocal s ⟨hs.1, hs.2.trans hwindow⟩

lemma cube_moment_integrable {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (n : ℕ) :
    IntegrableOn (fun s ↦ s ^ n * LowerProbability.cubeSlice d Δ s) (Ici (0 : ℝ)) := by
  have h := (LowerFubini.cubeSlice_mul_integrable (d := d) hΔ
    (f := fun s ↦ s ^ n) (by fun_prop)).integrableOn (s := Ici (0 : ℝ))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  simp only [abs_of_nonneg (show 0 ≤ s from hs)]

/-- The exact integration-to-covariance step: two actual slice envelopes yield
the genuine raw axial variance at order `r⁻²`, with explicit constants. -/
theorem rawAxialVariance_bounds_of_envelope {d : ℕ} {Δ r c C k : ℝ}
    (hΔ : 0 < Δ) (hroom : 0 < (d : ℝ) - 2 * Δ) (hr : 0 < r)
    (hc : 0 < c) (hC : 0 < C) (hk : 0 < k)
    (hm : 0 < LowerProbability.cubeSlice d Δ 0)
    (hlower : ∀ s ∈ Icc (0 : ℝ) (1 / r),
      c * LowerProbability.cubeSlice d Δ 0 ≤ LowerProbability.cubeSlice d Δ s)
    (hupper : ∀ s, 0 ≤ s → LowerProbability.cubeSlice d Δ s ≤
      C * LowerProbability.cubeSlice d Δ 0 * Real.exp (-k * r * s)) :
    (c * k / (3 * C)) / r ^ 2 ≤ rawAxialVariance d Δ ∧
      rawAxialVariance d Δ ≤ (2 * C / (c * k ^ 3)) / r ^ 2 := by
  let m := LowerProbability.cubeSlice d Δ 0
  let M₀ := moment 0 (LowerProbability.cubeSlice d Δ)
  let M₂ := moment 2 (LowerProbability.cubeSlice d Δ)
  have h0l : c * m / r ≤ M₀ := by
    simpa only [Nat.cast_zero, zero_add, one_mul, pow_one] using
      moment_lower hr (cube_moment_integrable hΔ 0)
        (fun s _ ↦ LowerFubini.cubeSlice_nonneg d Δ s) hlower
  have h0u : M₀ ≤ C * m / (k * r) := by
    simpa only [Nat.factorial_zero, Nat.cast_one, mul_one, zero_add, pow_one] using
      moment_upper hr hk (cube_moment_integrable hΔ 0) hupper
  have h2l : c * m / (3 * r ^ 3) ≤ M₂ := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℕ) + 1 = 3 from rfl] using
      moment_lower hr (cube_moment_integrable hΔ 2)
        (fun s _ ↦ LowerFubini.cubeSlice_nonneg d Δ s) hlower
  have h2u : M₂ ≤ 2 * C * m / (k * r) ^ 3 := by
    have h := moment_upper hr hk (cube_moment_integrable hΔ 2) hupper
    norm_num [Nat.factorial] at h
    convert h using 1 <;> ring
  have hm0 : 0 < M₀ := lt_of_lt_of_le (by dsimp [m]; positivity) h0l
  have heq : rawAxialVariance d Δ = M₂ / M₀ := by
    rw [LowerFubini.rawAxialVariance_eq_halfline_slice_ratio hΔ hroom]
    simp only [M₂, M₀, moment, pow_zero, one_mul]
  rw [heq]
  constructor
  · apply (le_div_iff₀ hm0).mpr
    calc
      _ ≤ ((c * k / (3 * C)) / r ^ 2) * (C * m / (k * r)) :=
        mul_le_mul_of_nonneg_left h0u (by positivity)
      _ = c * m / (3 * r ^ 3) := by field_simp
      _ ≤ M₂ := h2l
  · apply (div_le_iff₀ hm0).mpr
    calc
      M₂ ≤ 2 * C * m / (k * r) ^ 3 := h2u
      _ = ((2 * C / (c * k ^ 3)) / r ^ 2) * (c * m / r) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h0l (by positivity)

end SliceMoments
end GaussianTilt
