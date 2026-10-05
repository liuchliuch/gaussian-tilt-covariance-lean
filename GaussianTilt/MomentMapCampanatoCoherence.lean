import GaussianTilt.MomentMapCampanatoLimits

/-! # Geometric approximation itself gives convergent quadratic jets -/
noncomputable section
open Set Filter
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- No coefficient estimates are assumed: all three coherent geometric
rates follow from the genuine uniform approximations on nested balls. -/
theorem geometric_quadratic_approximations_coherent
    (f : E n → ℝ) (a : ℕ → ℝ) (p : ℕ → E n) (H : ℕ → E n →L[ℝ] E n)
    {R ρ q C : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hs : ∀ k v w, inner ℝ (H k v) w = inner ℝ v (H k w))
    (happrox : ∀ k, ∀ h : E n, ‖h‖ ≤ R * ρ ^ k →
      |f h - quadraticJet (a k) (p k) 0 (H k) h| ≤ C * (ρ ^ 2 * q) ^ k) :
    (∀ k, |a k - a (k + 1)| ≤ (C * (1 + ρ ^ 2 * q)) * (ρ ^ 2 * q) ^ k) ∧
    (∀ k, ‖p k - p (k + 1)‖ ≤ (C * (1 + ρ ^ 2 * q) / (R * ρ)) * (ρ * q) ^ k) ∧
    (∀ k, ‖H k - H (k + 1)‖ ≤ (4 * C * (1 + ρ ^ 2 * q) / (R ^ 2 * ρ ^ 2)) * q ^ k) := by
  have hstep (k : ℕ) := quadraticJet_coherence (f := f)
    (a k) (a (k + 1)) (p k) (p (k + 1)) (H k) (H (k + 1)) (hs k) (hs (k + 1))
    (mul_pos hR (pow_pos hρ (k + 1)))
    (show 0 ≤ C * (ρ ^ 2 * q) ^ k by positivity)
    (show 0 ≤ C * (ρ ^ 2 * q) ^ (k + 1) by positivity)
    (fun h hh => happrox k h (hh.trans (by
      rw [pow_succ]
      nlinarith [mul_nonneg hR.le (pow_nonneg hρ.le k)])))
    (happrox (k + 1))
  have hsum (k : ℕ) : C * (ρ ^ 2 * q) ^ k + C * (ρ ^ 2 * q) ^ (k + 1) =
      (C * (1 + ρ ^ 2 * q)) * (ρ ^ 2 * q) ^ k := by rw [pow_succ]; ring
  have hpow (k : ℕ) : (ρ ^ 2 * q) ^ k = (ρ ^ k) ^ 2 * q ^ k := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm 2 k, pow_mul]
  refine ⟨fun k => by simpa only [hsum] using (hstep k).1, ?_, ?_⟩
  · intro k
    have hh := (hstep k).2.1
    rw [hsum] at hh
    convert hh using 1
    rw [hpow, mul_pow, pow_succ]
    field_simp
    <;> ring
  · intro k
    have hh := (hstep k).2.2
    rw [hsum] at hh
    convert hh using 1
    rw [hpow, pow_succ]
    field_simp
    <;> ring

/-- Literal geometric quadratic approximations have actual coefficient
limits, with symmetry preserved. -/
theorem geometric_quadratic_approximations_have_limits
    (f : E n → ℝ) (a : ℕ → ℝ) (p : ℕ → E n) (H : ℕ → E n →L[ℝ] E n)
    {R ρ q C : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hs : ∀ k v w, inner ℝ (H k v) w = inner ℝ v (H k w))
    (happrox : ∀ k, ∀ h : E n, ‖h‖ ≤ R * ρ ^ k →
      |f h - quadraticJet (a k) (p k) 0 (H k) h| ≤ C * (ρ ^ 2 * q) ^ k) :
    ∃ a₀ : ℝ, ∃ p₀ : E n, ∃ H₀ : E n →L[ℝ] E n,
      Tendsto a atTop (𝓝 a₀) ∧ Tendsto p atTop (𝓝 p₀) ∧ Tendsto H atTop (𝓝 H₀) ∧
      (∀ v w, inner ℝ (H₀ v) w = inner ℝ v (H₀ w)) ∧
      (∀ k, |a k - a₀| ≤ (C * (1 + ρ ^ 2 * q)) * (ρ ^ 2 * q) ^ k / (1 - ρ ^ 2 * q)) ∧
      (∀ k, ‖p k - p₀‖ ≤ (C * (1 + ρ ^ 2 * q) / (R * ρ)) * (ρ * q) ^ k / (1 - ρ * q)) ∧
      (∀ k, ‖H k - H₀‖ ≤ (4 * C * (1 + ρ ^ 2 * q) / (R ^ 2 * ρ ^ 2)) * q ^ k / (1 - q)) := by
  obtain ⟨ha, hp, hH⟩ := geometric_quadratic_approximations_coherent f a p H hR hρ hρ1 hq.le hC hs happrox
  exact exists_quadratic_jet_limit a p H hρ hρ1 hq hq1 ha hp hH hs

end GaussianTilt.MomentMapRegularity
