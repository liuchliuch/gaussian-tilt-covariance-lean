import GaussianTilt.MomentMapRegularityInteriorDifferentiability

/-!
# Actual directional slope contraction from section balance

This is the scalar geometric contraction underlying the Hölder iteration.
It works directly with supporting planes, even before differentiability.
The inner radius is `θ r / 4`; the oscillation contracts by `1 - θ / 8`.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma supportsAt_line_inequality {φ : E n → ℝ} {x v p : E n} {s : ℝ}
    (hp : SupportsAt φ p (x + s • v)) (t : ℝ) :
    φ (x + s • v) + (t - s) * inner ℝ p v ≤ φ (x + t • v) := by
  have h := hp (x + t • v)
  have he : (x + t • v) - (x + s • v) = (t - s) • v := by module
  simpa only [he, inner_smul_right] using h

lemma supportsAt_directional_mono {φ : E n → ℝ} {x v p q : E n} {s t : ℝ}
    (hp : SupportsAt φ p (x + s • v)) (hq : SupportsAt φ q (x + t • v))
    (hst : s < t) : inner ℝ p v ≤ inner ℝ q v := by
  have hpt := supportsAt_line_inequality hp t
  have hqs := supportsAt_line_inequality hq s
  nlinarith

/-- The elementary real inequality behind directional contraction. The
reflected endpoint lies a definite distance beyond the inner left endpoint,
so a secant averaging inequality loses a fixed fraction of the oscillation. -/
lemma reflected_secant_oscillation_contraction {θ r A a b B : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r)
    (hAa : A ≤ a) (haB : a ≤ B)
    (hsecant : (r - (θ * r / 4 - θ * (r - θ * r / 4))) * b ≤
      (-(θ * r / 4) - (θ * r / 4 - θ * (r - θ * r / 4))) * a +
        (r + θ * r / 4) * B) :
    b - a ≤ (1 - θ / 8) * (B - A) := by
  let s := θ * r / 4
  let w := s - θ * (r - s)
  let D := r - w
  let k := 1 - θ / 8
  have hs : 0 < s := by dsimp [s]; positivity
  have hsr : s ≤ r / 4 := by dsimp [s]; nlinarith
  have hgap : θ * r / 4 ≤ -s - w := by
    have hh := mul_nonneg (mul_nonneg hθ.le hr.le) (sub_nonneg.mpr hθ1)
    dsimp [s, w]
    nlinarith
  have hw : w < 0 := by dsimp [s] at hs; dsimp [w, s] at hgap ⊢; nlinarith
  have hD : 0 < D := by dsimp [D]; linarith
  have hDupper : D ≤ 2 * r := by
    have hh := mul_nonneg (sub_nonneg.mpr hθ1) hr.le
    have hsθ := mul_nonneg hs.le (show 0 ≤ 1 + θ by linarith)
    dsimp [D, w]
    nlinarith
  have hk : 0 ≤ k := by dsimp [k]; linarith
  have hfactor : r + s ≤ k * D := by
    have hmul := mul_le_mul_of_nonneg_left hDupper hθ.le
    change r + s ≤ (1 - θ / 8) * (r - w)
    dsimp [D] at hmul
    nlinarith
  have hsec : D * (b - a) ≤ (r + s) * (B - a) := by
    change (r - (s - θ * (r - s))) * b ≤ (-s - (s - θ * (r - s))) * a + (r + s) * B at hsecant
    dsimp [D, w]
    nlinarith
  have hinner : b - a ≤ k * (B - a) := by
    apply (mul_le_mul_left hD).mp
    calc
      D * (b - a) ≤ (r + s) * (B - a) := hsec
      _ ≤ (k * D) * (B - a) := mul_le_mul_of_nonneg_right hfactor (sub_nonneg.mpr haB)
      _ = D * (k * (B - a)) := by ring
  exact hinner.trans (mul_le_mul_of_nonneg_left (by linarith : B - a ≤ B - A) hk)

/-- Four genuine supporting planes and the reflected actual section give
an oscillation contraction for their directional slopes. -/
theorem directional_support_oscillation_contraction {φ : E n → ℝ}
    {x v p₀ p₁ p₂ p₃ : E n} {θ r : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r)
    (hp₀ : SupportsAt φ p₀ (x + (-r) • v))
    (hp₁ : SupportsAt φ p₁ (x + (-(θ * r / 4)) • v))
    (hp₂ : SupportsAt φ p₂ (x + (θ * r / 4) • v))
    (hp₃ : SupportsAt φ p₃ (x + r • v))
    (hreflect : supportResidual φ p₂ (x + (θ * r / 4) • v)
        (x + (θ * r / 4 - θ * (r - θ * r / 4)) • v) ≤
      supportResidual φ p₂ (x + (θ * r / 4) • v) (x + r • v)) :
    inner ℝ (p₂ - p₁) v ≤ (1 - θ / 8) * inner ℝ (p₃ - p₀) v := by
  let s := θ * r / 4
  let w := s - θ * (r - s)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsr : s < r := by
    have hh := mul_le_mul_of_nonneg_right hθ1 hr.le
    dsimp [s]
    nlinarith
  have hAa := supportsAt_directional_mono hp₀ hp₁ (by change -r < -s; linarith)
  have haB := supportsAt_directional_mono hp₁ hp₃ (by change -s < r; linarith)
  have hleft := supportsAt_line_inequality hp₁ w
  have hright := supportsAt_line_inequality hp₃ (-s)
  have he (t : ℝ) : (x + t • v) - (x + s • v) = (t - s) • v := by module
  have href : (r - w) * inner ℝ p₂ v ≤ φ (x + r • v) - φ (x + w • v) := by
    change supportResidual φ p₂ (x + s • v) (x + w • v) ≤
      supportResidual φ p₂ (x + s • v) (x + r • v) at hreflect
    simp only [supportResidual, he, inner_smul_right] at hreflect
    nlinarith
  have hsec : (r - w) * inner ℝ p₂ v ≤
      (-s - w) * inner ℝ p₁ v + (r + s) * inner ℝ p₃ v := by
    change φ (x + -s • v) + (w - -s) * inner ℝ p₁ v ≤ φ (x + w • v) at hleft
    nlinarith
  rw [inner_sub_left, inner_sub_left]
  exact reflected_secant_oscillation_contraction hθ hθ1 hr hAa haB hsec

/-- Uniform balance of small actual sections gives the contraction above
whenever the displayed section height lies below the allowed cutoff. -/
theorem directional_support_oscillation_contraction_of_balance {φ : E n → ℝ}
    (hc : StrictConvexOn ℝ univ φ) {x v p₀ p₁ p₂ p₃ : E n} {θ r h₀ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r) (hv : v ≠ 0)
    (hp₀ : SupportsAt φ p₀ (x + (-r) • v))
    (hp₁ : SupportsAt φ p₁ (x + (-(θ * r / 4)) • v))
    (hp₂ : SupportsAt φ p₂ (x + (θ * r / 4) • v))
    (hp₃ : SupportsAt φ p₃ (x + r • v))
    (hheight : supportResidual φ p₂ (x + (θ * r / 4) • v) (x + r • v) < h₀)
    (hbalance : ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ y ∈ supportSection φ p₂ (x + (θ * r / 4) • v) h,
        (x + (θ * r / 4) • v) - θ • (y - (x + (θ * r / 4) • v)) ∈
          supportSection φ p₂ (x + (θ * r / 4) • v) h) :
    inner ℝ (p₂ - p₁) v ≤ (1 - θ / 8) * inner ℝ (p₃ - p₀) v := by
  apply directional_support_oscillation_contraction hθ hθ1 hr hp₀ hp₁ hp₂ hp₃
  let s := θ * r / 4
  let h := supportResidual φ p₂ (x + s • v) (x + r • v)
  have hsr : s < r := by
    have hh := mul_le_mul_of_nonneg_right hθ1 hr.le
    dsimp [s]
    nlinarith
  have hne : x + r • v ≠ x + s • v := by
    intro he
    have hz : (r - s) • v = 0 := by
      have hh : (x + r • v) - (x + s • v) = (r - s) • v := by module
      rw [← hh, he, sub_self]
    exact (smul_ne_zero (sub_pos.mpr hsr).ne' hv) hz
  have hh : 0 < h := strict_supportResidual_pos hc hp₂ hne
  have hmem := hbalance h hh hheight (x + r • v) (le_refl h)
  have he : (x + s • v) - θ • ((x + r • v) - (x + s • v)) =
      x + (s - θ * (r - s)) • v := by module
  rw [he] at hmem
  exact hmem

end GaussianTilt.MomentMapRegularity
