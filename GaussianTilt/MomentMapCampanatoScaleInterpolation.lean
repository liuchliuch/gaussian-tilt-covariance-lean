import GaussianTilt.MomentMapRegularityHolderIteration

/-! # All-radius interpolation of actual geometric approximation errors -/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapRegularity

/-- A uniform bound on every geometric ball supplies a bound at every
radius. This uses actual errors, without an assumed monotone supremum. -/
theorem geometric_ball_error_holder {F : Type*} [NormedAddCommGroup F]
    {f : F → ℝ} {R ρ q C : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hq : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hf : ∀ k : ℕ, ∀ h : F, ‖h‖ ≤ R * ρ ^ k → |f h| ≤ C * q ^ k)
    (h : F) (hh : ‖h‖ ≤ R) :
    |f h| ≤ q⁻¹ * C * (‖h‖ / R) ^ oscillationExponent ρ q := by
  have hα := oscillationExponent_pos hρ hρ1 hq hq1
  by_cases hz : h = 0
  · subst h
    simp only [norm_zero, zero_div, Real.zero_rpow hα.ne', mul_zero]
    have ht : Tendsto (fun k : ℕ => C * q ^ k) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds ht
      (Eventually.of_forall (fun k => hf k 0 (by simp; positivity)))
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hz
  have hx : 0 < ‖h‖ / R := div_pos hnorm hR
  obtain ⟨k, hkl, hku⟩ := exists_nat_pow_near_of_lt_one hx ((div_le_one hR).mpr hh) hρ hρ1
  have hp : q ^ (k + 1) ≤ (‖h‖ / R) ^ oscillationExponent ρ q := by
    have he : (ρ ^ (k + 1) : ℝ) ^ oscillationExponent ρ q = q ^ (k + 1) := by
      rw [← Real.rpow_natCast ρ (k + 1), ← Real.rpow_mul hρ.le]
      rw [mul_comm (↑(k + 1) : ℝ) (oscillationExponent ρ q), Real.rpow_mul hρ.le,
        rpow_oscillationExponent hρ hρ1 hq, Real.rpow_natCast]
    rw [← he]
    exact Real.rpow_le_rpow (pow_nonneg hρ.le _) hkl.le hα.le
  have hpow : q ^ k ≤ q⁻¹ * (‖h‖ / R) ^ oscillationExponent ρ q := by
    have hp' := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hq.le)
    have he : q⁻¹ * q ^ (k + 1) = q ^ k := by rw [pow_succ]; field_simp
    rwa [he] at hp'
  have hrad : ‖h‖ ≤ R * ρ ^ k := by
    have ht := (div_le_iff₀ hR).mp hku
    rwa [mul_comm] at ht
  calc
    |f h| ≤ C * q ^ k := hf k h hrad
    _ ≤ C * (q⁻¹ * (‖h‖ / R) ^ oscillationExponent ρ q) := mul_le_mul_of_nonneg_left hpow hC
    _ = _ := by ring

lemma oscillationExponent_quadratic (hρ : 0 < ρ) (hρ1 : ρ < 1) {q : ℝ} (hq : 0 < q) :
    oscillationExponent ρ (ρ ^ 2 * q) = 2 + oscillationExponent ρ q := by
  unfold oscillationExponent
  rw [Real.log_mul (pow_ne_zero 2 hρ.ne') hq.ne', Real.log_pow]
  have hn : Real.log ρ ≠ 0 := (Real.log_neg hρ hρ1).ne
  field_simp
  <;> ring

end GaussianTilt.MomentMapRegularity
