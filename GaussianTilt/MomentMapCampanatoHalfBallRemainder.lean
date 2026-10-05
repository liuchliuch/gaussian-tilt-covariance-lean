import GaussianTilt.MomentMapCampanatoHalfBallLimits

/-! # The limit jets genuinely approximate the original function -/
noncomputable section
open Set Filter
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Explicit coefficient tail estimates transfer the original approximation
to the constructed limit polynomial at every actual geometric scale. -/
theorem quadraticJet_halfBall_limit_remainder_on_scales
    (j : Fin n) (f : E n → ℝ) (a : ℕ → ℝ) (p : ℕ → E n) (H : ℕ → E n →L[ℝ] E n)
    (a₀ : ℝ) (p₀ : E n) (H₀ : E n →L[ℝ] E n)
    {R ρ q C A P K : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (hq : 0 ≤ q)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (happrox : ∀ k, ∀ h : E n, ‖h‖ ≤ R * ρ ^ k → 0 ≤ h j →
      |f h - quadraticJet (a k) (p k) 0 (H k) h| ≤ C * (ρ ^ 2 * q) ^ k)
    (ha : ∀ k, |a k - a₀| ≤ A * (ρ ^ 2 * q) ^ k)
    (hp : ∀ k, ‖p k - p₀‖ ≤ P * (ρ * q) ^ k)
    (hH : ∀ k, ‖H k - H₀‖ ≤ K * q ^ k) :
    ∀ k, ∀ h : E n, ‖h‖ ≤ R * ρ ^ k → 0 ≤ h j →
      |f h - quadraticJet a₀ p₀ 0 H₀ h| ≤
        (C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2) * (ρ ^ 2 * q) ^ k := by
  intro k h hh hj
  have hpB : ‖p k - p₀‖ * ‖h‖ ≤ (P * (ρ * q) ^ k) * (R * ρ ^ k) :=
    mul_le_mul (hp k) hh (norm_nonneg _) (by positivity)
  have hs : ‖h‖ ^ 2 ≤ (R * ρ ^ k) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
  have hHB : ‖H k - H₀‖ * ‖h‖ ^ 2 ≤ (K * q ^ k) * (R * ρ ^ k) ^ 2 :=
    mul_le_mul (hH k) hs (sq_nonneg _) (by positivity)
  have hpoly := quadraticJet_abs_le (a k - a₀) (p k - p₀) h (H k - H₀)
  have he := abs_sub_le (f h) (quadraticJet (a k) (p k) 0 (H k) h) (quadraticJet a₀ p₀ 0 H₀ h)
  rw [quadraticJet_sub] at he
  have hscale : C * (ρ ^ 2 * q) ^ k + A * (ρ ^ 2 * q) ^ k +
      (P * (ρ * q) ^ k) * (R * ρ ^ k) +
      (1 / 2 : ℝ) * ((K * q ^ k) * (R * ρ ^ k) ^ 2) =
        (C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2) * (ρ ^ 2 * q) ^ k := by
    simp only [mul_pow, ← pow_mul]
    rw [Nat.mul_comm 2 k]
    ring
  rw [← hscale]
  linarith [happrox k h hh hj, ha k]

end GaussianTilt.MomentMapRegularity
