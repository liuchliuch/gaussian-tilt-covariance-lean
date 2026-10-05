import Mathlib

/-! # Geometric oscillation decay gives a genuine Hölder modulus

The radius is located between two actual geometric scales. Iterating the
one-step contraction and evaluating the logarithmic exponent supplies the
uniform power bound without assuming a Hölder conclusion.
-/
noncomputable section
open Set

namespace GaussianTilt.MomentMapRegularity

def oscillationExponent (a q : ℝ) : ℝ := Real.log q / Real.log a

lemma oscillationExponent_pos {a q : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hq : 0 < q) (hq1 : q < 1) : 0 < oscillationExponent a q :=
  div_pos_of_neg_of_neg (Real.log_neg hq hq1) (Real.log_neg ha ha1)

lemma oscillationExponent_le_one {a q : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (haq : a ≤ q) : oscillationExponent a q ≤ 1 := by
  apply (div_le_iff_of_neg (Real.log_neg ha ha1)).mpr
  simpa only [one_mul] using Real.log_le_log ha haq

lemma rpow_oscillationExponent {a q : ℝ} (ha : 0 < a) (ha1 : a < 1) (hq : 0 < q) :
    a ^ oscillationExponent a q = q := by
  rw [Real.rpow_def_of_pos ha]
  have he : Real.log a * oscillationExponent a q = Real.log q := by
    unfold oscillationExponent
    field_simp [(Real.log_neg ha ha1).ne]
  rw [he, Real.exp_log hq]

lemma geometric_oscillation_decay {ω : ℝ → ℝ} {a q R : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hq : 0 ≤ q) (hR : 0 < R)
    (hstep : ∀ r ∈ Ioc 0 R, ω (a * r) ≤ q * ω r) (k : ℕ) :
    ω (a ^ k * R) ≤ q ^ k * ω R := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hr : a ^ k * R ∈ Ioc 0 R :=
        ⟨mul_pos (pow_pos ha k) hR,
          (mul_le_mul_of_nonneg_right (pow_le_one₀ ha.le ha1.le) hR.le).trans_eq (one_mul R)⟩
      calc
        ω (a ^ (k + 1) * R) = ω (a * (a ^ k * R)) := by congr 1; rw [pow_succ]; ring
        _ ≤ q * ω (a ^ k * R) := hstep _ hr
        _ ≤ q * (q ^ k * ω R) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (k + 1) * ω R := by rw [pow_succ]; ring

/-- Uniform power decay at every radius, not merely at discrete scales. -/
theorem oscillation_holder_of_geometric_decay {ω : ℝ → ℝ} {a q R : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hq : 0 < q) (hq1 : q < 1) (hR : 0 < R)
    (hωR : 0 ≤ ω R) (hmono : MonotoneOn ω (Ioc 0 R))
    (hstep : ∀ r ∈ Ioc 0 R, ω (a * r) ≤ q * ω r)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ω r ≤ q⁻¹ * ω R * (r / R) ^ oscillationExponent a q := by
  have hx : 0 < r / R := div_pos hr hR
  have hx1 : r / R ≤ 1 := (div_le_one hR).mpr hrR
  obtain ⟨k, hkl, hku⟩ := exists_nat_pow_near_of_lt_one hx hx1 ha ha1
  have hkR : a ^ k * R ∈ Ioc 0 R :=
    ⟨mul_pos (pow_pos ha k) hR,
      (mul_le_mul_of_nonneg_right (pow_le_one₀ ha.le ha1.le) hR.le).trans_eq (one_mul R)⟩
  have hm : ω r ≤ ω (a ^ k * R) := hmono ⟨hr, hrR⟩ hkR ((div_le_iff₀ hR).mp hku)
  have hα := oscillationExponent_pos ha ha1 hq hq1
  have hp : q ^ (k + 1) ≤ (r / R) ^ oscillationExponent a q := by
    have he : (a ^ (k + 1) : ℝ) ^ oscillationExponent a q = q ^ (k + 1) := by
      rw [← Real.rpow_natCast a (k + 1), ← Real.rpow_mul ha.le]
      rw [mul_comm (↑(k + 1) : ℝ) (oscillationExponent a q), Real.rpow_mul ha.le,
        rpow_oscillationExponent ha ha1 hq, Real.rpow_natCast]
    rw [← he]
    exact Real.rpow_le_rpow (pow_nonneg ha.le _) hkl.le hα.le
  have hpow : q ^ k ≤ q⁻¹ * (r / R) ^ oscillationExponent a q := by
    have h := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hq.le)
    have he : q⁻¹ * q ^ (k + 1) = q ^ k := by rw [pow_succ]; field_simp
    rwa [he] at h
  calc
    ω r ≤ ω (a ^ k * R) := hm
    _ ≤ q ^ k * ω R := geometric_oscillation_decay ha ha1 hq.le hR hstep k
    _ ≤ (q⁻¹ * (r / R) ^ oscillationExponent a q) * ω R :=
      mul_le_mul_of_nonneg_right hpow hωR
    _ = _ := by ring

/-- The section-reflection constants used by the Caffarelli iteration give
a real exponent in `(0,1]`, with the exact quantitative modulus. -/
theorem reflected_oscillation_holder {ω : ℝ → ℝ} {θ R : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hR : 0 < R) (hωR : 0 ≤ ω R)
    (hmono : MonotoneOn ω (Ioc 0 R))
    (hstep : ∀ r ∈ Ioc 0 R, ω ((θ / 4) * r) ≤ (1 - θ / 8) * ω r) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ r ∈ Ioc 0 R,
      ω r ≤ (1 - θ / 8)⁻¹ * ω R * (r / R) ^ α := by
  have ha : 0 < θ / 4 := by positivity
  have ha1 : θ / 4 < 1 := by linarith
  have hq : 0 < 1 - θ / 8 := by linarith
  have hq1 : 1 - θ / 8 < 1 := by linarith
  refine ⟨oscillationExponent (θ / 4) (1 - θ / 8), oscillationExponent_pos ha ha1 hq hq1,
    oscillationExponent_le_one ha ha1 (by linarith), ?_⟩
  intro r hr
  exact oscillation_holder_of_geometric_decay ha ha1 hq hq1 hR hωR hmono hstep hr.1 hr.2

end GaussianTilt.MomentMapRegularity
