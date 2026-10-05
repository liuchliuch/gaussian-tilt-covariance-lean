import GaussianTilt.MomentMapCampanatoLimitApproximation
import GaussianTilt.MomentMapCampanatoScaleInterpolation
import GaussianTilt.MomentMapCampanatoHolderJets

/-! # The full geometric quadratic approximation endpoint -/
noncomputable section
open Set Filter
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def campanatoLimitConstant (R ρ q C : ℝ) : ℝ :=
  let A := C * (1 + ρ ^ 2 * q) / (1 - ρ ^ 2 * q)
  let P := (C * (1 + ρ ^ 2 * q) / (R * ρ)) / (1 - ρ * q)
  let K := (4 * C * (1 + ρ ^ 2 * q) / (R ^ 2 * ρ ^ 2)) / (1 - q)
  (ρ ^ 2 * q)⁻¹ * (C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2) /
    R ^ (2 + oscillationExponent ρ q)

/-- Geometric uniform quadratic approximations yield a genuine limiting
quadratic expansion with an all-radius positive-order remainder. -/
theorem geometric_quadratic_approximation_endpoint
    (f : E n → ℝ) (a : ℕ → ℝ) (p : ℕ → E n) (H : ℕ → E n →L[ℝ] E n)
    {R ρ q C : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hs : ∀ k v w, inner ℝ (H k v) w = inner ℝ v (H k w))
    (happrox : ∀ k, ∀ h : E n, ‖h‖ ≤ R * ρ ^ k →
      |f h - quadraticJet (a k) (p k) 0 (H k) h| ≤ C * (ρ ^ 2 * q) ^ k) :
    0 ≤ campanatoLimitConstant R ρ q C ∧
      ∃ a₀ : ℝ, ∃ p₀ : E n, ∃ H₀ : E n →L[ℝ] E n,
        (∀ v w, inner ℝ (H₀ v) w = inner ℝ v (H₀ w)) ∧
        ∀ h : E n, ‖h‖ ≤ R → |f h - quadraticJet a₀ p₀ 0 H₀ h| ≤
          campanatoLimitConstant R ρ q C * ‖h‖ ^ (2 + oscillationExponent ρ q) := by
  have hρq : ρ * q < 1 := by nlinarith
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hρ2q : ρ ^ 2 * q < 1 := by nlinarith
  have hqa : 0 < ρ ^ 2 * q := mul_pos (sq_pos_of_pos hρ) hq
  have hdA : 0 < 1 - ρ ^ 2 * q := sub_pos.mpr hρ2q
  have hdP : 0 < 1 - ρ * q := sub_pos.mpr hρq
  have hdK : 0 < 1 - q := sub_pos.mpr hq1
  let A := C * (1 + ρ ^ 2 * q) / (1 - ρ ^ 2 * q)
  let P := (C * (1 + ρ ^ 2 * q) / (R * ρ)) / (1 - ρ * q)
  let K := (4 * C * (1 + ρ ^ 2 * q) / (R ^ 2 * ρ ^ 2)) / (1 - q)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2 := by positivity
  have hconst : 0 ≤ campanatoLimitConstant R ρ q C := by
    change 0 ≤ (ρ ^ 2 * q)⁻¹ * (C + A + P * R + (1 / 2 : ℝ) * K * R ^ 2) /
      R ^ (2 + oscillationExponent ρ q)
    positivity
  refine ⟨hconst, ?_⟩
  obtain ⟨a₀, p₀, H₀, hat, hpt, hHt, hs₀, hab, hpb, hHb⟩ :=
    geometric_quadratic_approximations_have_limits f a p H hR hρ hρ1 hq hq1 hC hs happrox
  have ha : ∀ k, |a k - a₀| ≤ A * (ρ ^ 2 * q) ^ k := by
    intro k
    simpa only [A, div_mul_eq_mul_div] using hab k
  have hp : ∀ k, ‖p k - p₀‖ ≤ P * (ρ * q) ^ k := by
    intro k
    simpa only [P, div_mul_eq_mul_div] using hpb k
  have hH : ∀ k, ‖H k - H₀‖ ≤ K * q ^ k := by
    intro k
    simpa only [K, div_mul_eq_mul_div] using hHb k
  have hscale := quadraticJet_limit_remainder_on_scales f a p H a₀ p₀ H₀
    hR.le hρ.le hq.le hA hP hK happrox ha hp hH
  refine ⟨a₀, p₀, H₀, hs₀, ?_⟩
  intro h hh
  have hall := geometric_ball_error_holder hR hρ hρ1 hqa hρ2q hD hscale h hh
  rw [oscillationExponent_quadratic hρ hρ1 hq,
    Real.div_rpow (norm_nonneg h) hR.le] at hall
  convert hall using 1
  dsimp [campanatoLimitConstant, A, P, K]
  ring

/-- Complete Campanato criterion: actual geometric quadratic approximations
uniform in the center produce genuine C² regularity and an actual locally
Hölder Hessian. No jets, derivative field, or regularity conclusion are assumed. -/
theorem contDiffOn_two_of_geometric_quadratic_approximations
    {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    {U : Set (E n)} (hU : IsOpen U)
    {R ρ q C : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (happrox : ∀ x ∈ U, ∃ a : ℕ → ℝ, ∃ p : ℕ → E n, ∃ H : ℕ → E n →L[ℝ] E n,
      (∀ k v w, inner ℝ (H k v) w = inner ℝ v (H k w)) ∧
      ∀ k, ∀ h : E n, ‖h‖ ≤ R * ρ ^ k →
        |u (x + h) - quadraticJet (a k) (p k) 0 (H k) h| ≤ C * (ρ ^ 2 * q) ^ k) :
    ContDiffOn ℝ 2 u U ∧
      ∃ H : E n → E n →L[ℝ] E n,
        (∀ x ∈ U, HasFDerivAt (gradient u) (H x) x) ∧
        ∀ x ∈ U, ∀ y ∈ U, 2 * ‖x - y‖ ≤ R →
          ‖H x - H y‖ ≤
            (4 * campanatoLimitConstant R ρ q C * (1 + (2 : ℝ) ^ (2 + oscillationExponent ρ q))) *
              ‖x - y‖ ^ oscillationExponent ρ q := by
  have hα := oscillationExponent_pos hρ hρ1 hq hq1
  have hL : 0 ≤ campanatoLimitConstant R ρ q C := by
    unfold campanatoLimitConstant
    have hp : ρ * q < 1 := by nlinarith
    have hp2 : ρ ^ 2 * q < 1 := by
      have : ρ ^ 2 < 1 := by nlinarith
      nlinarith
    have h₁ := sub_pos.mpr hp
    have h₂ := sub_pos.mpr hp2
    have h₃ := sub_pos.mpr hq1
    positivity
  have hex : ∀ x : E n, ∃ H₀ : E n →L[ℝ] E n, x ∈ U →
      (∀ v w, inner ℝ (H₀ v) w = inner ℝ v (H₀ w)) ∧
      ∀ z : E n, ‖z - x‖ ≤ R →
        |u z - quadraticJet (u x) (gradient u x) x H₀ z| ≤
          campanatoLimitConstant R ρ q C * ‖z - x‖ ^ (2 + oscillationExponent ρ q) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨a, p, H, hs, happ⟩ := happrox x hx
      obtain ⟨_, a₀, p₀, H₀, hs₀, he⟩ := geometric_quadratic_approximation_endpoint
        (fun h => u (x + h)) a p H hR hρ hρ1 hq hq1 hC hs happ
      have he' : ∀ z : E n, ‖z - x‖ ≤ R →
          |u z - quadraticJet a₀ p₀ x H₀ z| ≤
            campanatoLimitConstant R ρ q C * ‖z - x‖ ^ (2 + oscillationExponent ρ q) := by
        intro z hz
        have hez := he (z - x) hz
        simpa only [quadraticJet, sub_zero, add_sub_cancel] using hez
      obtain ⟨ha, hp⟩ := quadratic_linear_coefficient_eq_gradient hu hd a₀ p₀ x H₀ hs₀ hα hR hL he'
      exact ⟨H₀, fun _ => ⟨hs₀, by simpa only [ha, hp] using he'⟩⟩
    · exact ⟨0, fun h => False.elim (hx h)⟩
  choose H hH using hex
  have hs : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w) := fun x hx => (hH x hx).1
  have he := fun x hx => (hH x hx).2
  obtain ⟨hc, hdH⟩ := contDiffOn_two_of_uniform_holder_quadratic_remainders hu hd hU H hR hL hα hs he
  refine ⟨hc, H, hdH, ?_⟩
  intro x hx y hy hxy
  exact quadratic_coefficients_holder_of_uniform_remainder u (gradient u) H hL hα hs he hx hy hxy

end GaussianTilt.MomentMapRegularity
