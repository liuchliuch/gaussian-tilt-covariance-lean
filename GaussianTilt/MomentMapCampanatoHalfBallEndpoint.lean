import GaussianTilt.MomentMapCampanatoHalfBallRemainder
import GaussianTilt.MomentMapCampanatoScaleInterpolation
import GaussianTilt.MomentMapCampanatoHolderJets

/-! # The full geometric quadratic approximation endpoint -/
noncomputable section
open Set Filter
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def campanatoHalfBallLimitConstant (R ρ q C : ℝ) : ℝ :=
  let A := C * (1 + ρ ^ 2 * q) / (1 - ρ ^ 2 * q)
  let P := (36 * C * (1 + ρ ^ 2 * q) / (R * ρ)) / (1 - ρ * q)
  let K := (64 * C * (1 + ρ ^ 2 * q) / (R ^ 2 * ρ ^ 2)) / (1 - q)
  (ρ ^ 2 * q)⁻¹ * (C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2) /
    R ^ (2 + oscillationExponent ρ q)

/-- Geometric uniform quadratic approximations yield a genuine limiting
quadratic expansion with an all-radius positive-order remainder. -/
theorem geometric_halfBall_quadratic_approximation_endpoint_with_limits
    (j : Fin n) (f : E n → ℝ) (a : ℕ → ℝ) (p : ℕ → E n) (H : ℕ → E n →L[ℝ] E n)
    {R ρ q C : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hs : ∀ k v w, inner ℝ (H k v) w = inner ℝ v (H k w))
    (happrox : ∀ k, ∀ h : E n, ‖h‖ ≤ R * ρ ^ k → 0 ≤ h j →
      |f h - quadraticJet (a k) (p k) 0 (H k) h| ≤ C * (ρ ^ 2 * q) ^ k) :
    0 ≤ campanatoHalfBallLimitConstant R ρ q C ∧
      ∃ a₀ : ℝ, ∃ p₀ : E n, ∃ H₀ : E n →L[ℝ] E n,
        Tendsto a atTop (𝓝 a₀) ∧ Tendsto p atTop (𝓝 p₀) ∧ Tendsto H atTop (𝓝 H₀) ∧
        (∀ v w, inner ℝ (H₀ v) w = inner ℝ v (H₀ w)) ∧
        ∀ h : E n, ‖h‖ ≤ R → 0 ≤ h j → |f h - quadraticJet a₀ p₀ 0 H₀ h| ≤
          campanatoHalfBallLimitConstant R ρ q C * ‖h‖ ^ (2 + oscillationExponent ρ q) := by
  have hρq : ρ * q < 1 := by nlinarith
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hρ2q : ρ ^ 2 * q < 1 := by nlinarith
  have hqa : 0 < ρ ^ 2 * q := mul_pos (sq_pos_of_pos hρ) hq
  have hdA : 0 < 1 - ρ ^ 2 * q := sub_pos.mpr hρ2q
  have hdP : 0 < 1 - ρ * q := sub_pos.mpr hρq
  have hdK : 0 < 1 - q := sub_pos.mpr hq1
  let A := C * (1 + ρ ^ 2 * q) / (1 - ρ ^ 2 * q)
  let P := (36 * C * (1 + ρ ^ 2 * q) / (R * ρ)) / (1 - ρ * q)
  let K := (64 * C * (1 + ρ ^ 2 * q) / (R ^ 2 * ρ ^ 2)) / (1 - q)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2 := by positivity
  have hconst : 0 ≤ campanatoHalfBallLimitConstant R ρ q C := by
    change 0 ≤ (ρ ^ 2 * q)⁻¹ * (C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2) /
      R ^ (2 + oscillationExponent ρ q)
    positivity
  refine ⟨hconst, ?_⟩
  obtain ⟨a₀, p₀, H₀, hat, hpt, hHt, hs₀, hab, hpb, hHb⟩ :=
    geometric_halfBall_quadratic_approximations_have_limits j f a p H hR hρ hρ1 hq hq1 hC hs happrox
  have ha : ∀ k, |a k - a₀| ≤ A * (ρ ^ 2 * q) ^ k := by
    intro k
    simpa only [A, div_mul_eq_mul_div] using hab k
  have hp : ∀ k, ‖p k - p₀‖ ≤ P * (ρ * q) ^ k := by
    intro k
    simpa only [P, div_mul_eq_mul_div] using hpb k
  have hH : ∀ k, ‖H k - H₀‖ ≤ K * q ^ k := by
    intro k
    simpa only [K, div_mul_eq_mul_div] using hHb k
  have hscale := quadraticJet_halfBall_limit_remainder_on_scales j f a p H a₀ p₀ H₀
    hR.le hρ.le hq.le hA hP hK happrox ha hp hH
  refine ⟨a₀, p₀, H₀, hat, hpt, hHt, hs₀, ?_⟩
  intro h hh hj
  let err : E n → ℝ := fun z => if 0 ≤ z j then f z - quadraticJet a₀ p₀ 0 H₀ z else 0
  have herr : ∀ k, ∀ z : E n, ‖z‖ ≤ R * ρ ^ k →
      |err z| ≤ (C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2) * (ρ ^ 2 * q) ^ k := by
    intro k z hz
    by_cases hzj : 0 ≤ z j
    · simpa only [err, if_pos hzj] using hscale k z hz hzj
    · simp only [err, if_neg hzj, abs_zero]
      positivity
  have hall := geometric_ball_error_holder hR hρ hρ1 hqa hρ2q hD herr h hh
  simp only [err, if_pos hj] at hall
  rw [oscillationExponent_quadratic hρ hρ1 hq,
    Real.div_rpow (norm_nonneg h) hR.le] at hall
  convert hall using 1
  dsimp [campanatoHalfBallLimitConstant, A, P, K]
  ring


/-- The shorter expansion-only interface remains available. -/
theorem geometric_halfBall_quadratic_approximation_endpoint
    (j : Fin n) (f : E n → ℝ) (a : ℕ → ℝ) (p : ℕ → E n) (H : ℕ → E n →L[ℝ] E n)
    {R ρ q C : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hs : ∀ k v w, inner ℝ (H k v) w = inner ℝ v (H k w))
    (happrox : ∀ k, ∀ h : E n, ‖h‖ ≤ R * ρ ^ k → 0 ≤ h j →
      |f h - quadraticJet (a k) (p k) 0 (H k) h| ≤ C * (ρ ^ 2 * q) ^ k) :
    0 ≤ campanatoHalfBallLimitConstant R ρ q C ∧
      ∃ a₀ : ℝ, ∃ p₀ : E n, ∃ H₀ : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H₀ v) w = inner ℝ v (H₀ w)) ∧
        ∀ h : E n, ‖h‖ ≤ R → 0 ≤ h j → |f h - quadraticJet a₀ p₀ 0 H₀ h| ≤
          campanatoHalfBallLimitConstant R ρ q C * ‖h‖ ^ (2 + oscillationExponent ρ q) := by
  obtain ⟨hc, a₀, p₀, H₀, _, _, _, hs₀, he⟩ :=
    geometric_halfBall_quadratic_approximation_endpoint_with_limits j f a p H
      hR hρ hρ1 hq hq1 hC hs happrox
  exact ⟨hc, a₀, p₀, H₀, hs₀, he⟩

end GaussianTilt.MomentMapRegularity
