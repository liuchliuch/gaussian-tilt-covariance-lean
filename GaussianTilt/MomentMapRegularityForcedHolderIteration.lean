import GaussianTilt.MomentMapRegularityHolderIteration

/-! # Forced oscillation decay yields an actual Hölder modulus -/
noncomputable section
open Set
namespace GaussianTilt.MomentMapRegularity

/-- A linear forcing error is absorbed by the actual corrected oscillation
ω(r)+Mr/(q−a), reducing the iteration to the proved pure geometric case. -/
theorem oscillation_holder_of_forced_geometric_decay {ω : ℝ → ℝ} {a q R M : ℝ}
    (ha : 0 < a) (haq : a < q) (hq1 : q < 1) (hR : 0 < R) (hM : 0 ≤ M)
    (hωR : 0 ≤ ω R) (hmono : MonotoneOn ω (Ioc 0 R))
    (hstep : ∀ r ∈ Ioc 0 R, ω (a * r) ≤ q * ω r + M * r)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ω r ≤ q⁻¹ * (ω R + M * R / (q - a)) * (r / R) ^ oscillationExponent a q := by
  let K := M / (q - a)
  let Ω := fun t => ω t + K * t
  have hK : 0 ≤ K := div_nonneg hM (sub_pos.mpr haq).le
  have hKa : K * (q - a) = M := div_mul_cancel₀ M (sub_pos.mpr haq).ne'
  have hΩ : MonotoneOn Ω (Ioc 0 R) := by
    intro x hx y hy hxy
    exact add_le_add (hmono hx hy hxy) (mul_le_mul_of_nonneg_left hxy hK)
  have hΩstep : ∀ t ∈ Ioc 0 R, Ω (a * t) ≤ q * Ω t := by
    intro t ht
    have hh := hstep t ht
    have he : K * (a * t) + M * t = q * (K * t) := by nlinarith [congrArg (· * t) hKa]
    dsimp [Ω]
    nlinarith
  have hb := oscillation_holder_of_geometric_decay ha (haq.trans hq1) (ha.trans haq) hq1 hR
    (show 0 ≤ Ω R from add_nonneg hωR (mul_nonneg hK hR.le)) hΩ hΩstep hr hrR
  have hlo : ω r ≤ Ω r := le_add_of_nonneg_right (mul_nonneg hK hr.le)
  apply hlo.trans
  convert hb using 1
  dsimp [Ω, K]
  congr 2
  ring

/-- The flat boundary contraction scales give a universal explicit prefactor. -/
theorem eighth_scale_forced_oscillation_holder {ω : ℝ → ℝ} {q M : ℝ}
    (hq : (1 / 2 : ℝ) ≤ q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hω : 0 ≤ ω 1) (hmono : MonotoneOn ω (Ioc (0 : ℝ) 1))
    (hstep : ∀ r ∈ Ioc (0 : ℝ) 1, ω (r / 8) ≤ q * ω r + M * r) :
    0 < oscillationExponent (1 / 8) q ∧ oscillationExponent (1 / 8) q ≤ 1 ∧
      ∀ r ∈ Ioc (0 : ℝ) 1,
        ω r ≤ 8 * (ω 1 + M) * r ^ oscillationExponent (1 / 8) q := by
  have hq0 : 0 < q := by linarith
  have haq : (1 / 8 : ℝ) < q := by linarith
  refine ⟨oscillationExponent_pos (by norm_num) (by norm_num) hq0 hq1,
    oscillationExponent_le_one (by norm_num) (by norm_num) haq.le, ?_⟩
  intro r hr
  have hb := oscillation_holder_of_forced_geometric_decay (ω := ω) (a := 1 / 8)
    (by norm_num) haq hq1 (by norm_num : (0 : ℝ) < 1) hM hω hmono
    (fun t ht => by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hstep t ht) hr.1 hr.2
  simp only [mul_one, div_one] at hb
  have hden : 0 < q - 1 / 8 := sub_pos.mpr haq
  have hfrac : M / (q - 1 / 8) ≤ 4 * M := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hM (show 0 ≤ q - 1 / 2 by linarith)]
  have hinv : q⁻¹ ≤ 2 := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hq
    norm_num at hi
    simpa only [one_div] using hi
  have hcoef : q⁻¹ * (ω 1 + M / (q - 1 / 8)) ≤ 8 * (ω 1 + M) := by
    have hnn : 0 ≤ ω 1 + M / (q - 1 / 8) := add_nonneg hω (div_nonneg hM hden.le)
    nlinarith [mul_le_mul_of_nonneg_right hinv hnn]
  exact hb.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hr.1.le _))

end GaussianTilt.MomentMapRegularity
