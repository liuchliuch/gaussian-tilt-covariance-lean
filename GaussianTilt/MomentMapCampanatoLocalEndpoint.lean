import GaussianTilt.MomentMapCampanatoEndpoint
import GaussianTilt.MomentMapCampanatoLocalCriterion

/-! # The local geometric approximation criterion needs no global regularity -/
noncomputable section
open Set Filter
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Local, assumption-free Campanato endpoint. The function may be arbitrary
outside the approximation balls. Convexity, existing gradients and global
differentiability are not premises. Both actual derivatives are derived. -/
theorem contDiffOn_two_of_geometric_quadratic_approximations_local
    {u : E n → ℝ} {U : Set (E n)} (hU : IsOpen U)
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
  have hex : ∀ x : E n, ∃ a₀ : ℝ, ∃ p₀ : E n, ∃ H₀ : E n →L[ℝ] E n, x ∈ U →
      (∀ v w, inner ℝ (H₀ v) w = inner ℝ v (H₀ w)) ∧
      ∀ z : E n, ‖z - x‖ ≤ R →
        |u z - quadraticJet a₀ p₀ x H₀ z| ≤
          campanatoLimitConstant R ρ q C * ‖z - x‖ ^ (2 + oscillationExponent ρ q) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨a, p, H, hs, happ⟩ := happrox x hx
      obtain ⟨_, a₀, p₀, H₀, hs₀, he⟩ := geometric_quadratic_approximation_endpoint
        (fun h => u (x + h)) a p H hR hρ hρ1 hq hq1 hC hs happ
      refine ⟨a₀, p₀, H₀, fun _ => ⟨hs₀, ?_⟩⟩
      intro z hz
      have hez := he (z - x) hz
      simpa only [quadraticJet, sub_zero, add_sub_cancel] using hez
    · exact ⟨0, 0, 0, fun h => False.elim (hx h)⟩
  choose a p H hH using hex
  have hs : ∀ x ∈ U, ∀ v w, inner ℝ (H x v) w = inner ℝ v (H x w) := fun x hx => (hH x hx).1
  have he := fun x hx => (hH x hx).2
  obtain ⟨hc, hcoeff, hdH⟩ := contDiffOn_two_of_uniform_quadratic_remainders_local
    a p H hU hR hL hα hs he
  refine ⟨hc, H, hdH, ?_⟩
  intro x hx y hy hxy
  exact quadratic_coefficients_holder_of_uniform_remainder a p H hL hα hs he hx hy hxy

end GaussianTilt.MomentMapRegularity
