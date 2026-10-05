import GaussianTilt.MomentMapRegularityInteriorOscillation
import GaussianTilt.MomentMapRegularityAffineSectionBalance

/-!
# Uniform small-section geometry on compact source neighborhoods

Strict convexity separates every supporting plane from every sphere around
its center. Compactness of the full bounded support graph makes this
separation uniform over compact sets of centers, with no assumed gradient
continuity. A global Lipschitz bound also controls the actual section heights.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Strict supporting gaps on a fixed-radius sphere have a positive
uniform lower bound over a compact set of centers and all their supports. -/
theorem uniform_strict_supportResidual_sphere_gap {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : StrictConvexOn ℝ univ φ)
    {A : Set (E n)} (hA : IsCompact A) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ A, ∀ p, SupportsAt φ p x →
      ∀ y ∈ Metric.sphere x r, δ ≤ supportResidual φ p x y := by
  let G := (A ×ˢ Metric.closedBall (0 : E n) (L : ℝ)) ∩
    {z : E n × E n | SupportsAt φ z.2 z.1}
  let D := G ×ˢ Metric.sphere (0 : E n) r
  let F : (E n × E n) × E n → ℝ := fun z =>
    φ (z.1.1 + z.2) - φ z.1.1 - inner ℝ z.1.2 z.2
  have hG : IsCompact G := (hA.prod (isCompact_closedBall 0 (L : ℝ))).inter_right
    (isClosed_supportsAt_graph hL.continuous)
  have hD : IsCompact D := hG.prod (isCompact_sphere 0 r)
  have hF : Continuous F := by
    dsimp [F]
    exact ((hL.continuous.comp (continuous_fst.fst.add continuous_snd)).sub
      (hL.continuous.comp continuous_fst.fst)).sub (continuous_fst.snd.inner continuous_snd)
  have hFpos : ∀ z ∈ D, 0 < F z := by
    rintro ⟨⟨x, p⟩, v⟩ ⟨⟨⟨hx, hpL⟩, hp⟩, hv⟩
    have hvnorm : ‖v‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
    have hne : x + v ≠ x := by
      intro he
      have hv0 : v = 0 := add_left_cancel (show x + v = x + 0 by simpa using he)
      rw [hv0, norm_zero] at hvnorm
      exact hr.ne' hvnorm.symm
    have hh := strict_supportResidual_pos hc hp hne
    simpa only [supportResidual, add_sub_cancel_left] using hh
  have hmem (x : E n) (hx : x ∈ A) (p : E n) (hp : SupportsAt φ p x)
      (y : E n) (hy : y ∈ Metric.sphere x r) : ((x, p), y - x) ∈ D := by
    refine ⟨⟨⟨hx, ?_⟩, hp⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using supportsAt_norm_le hL hp
    · simpa only [Metric.mem_sphere, dist_zero_right, dist_eq_norm, sub_zero] using hy
  by_cases hn : D.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hD.exists_isMinOn hn hF.continuousOn
    refine ⟨F z, hFpos z hz, ?_⟩
    intro x hx p hp y hy
    have hh := hmin (hmem x hx p hp y hy)
    change F z ≤ F ((x, p), y - x) at hh
    have he : x + (y - x) = y := by module
    simpa only [F, he, supportResidual] using hh
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx p hp y hy
    exact (hn ⟨_, hmem x hx p hp y hy⟩).elim

/-- Actual strict-convex sections shrink uniformly for centers in compact
sets and for all actual supporting slopes. No support selection is used. -/
theorem uniform_small_supportSection_subset_ball {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : StrictConvexOn ℝ univ φ)
    {A : Set (E n)} (hA : IsCompact A) {r : ℝ} (hr : 0 < r) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ x ∈ A, ∀ p, SupportsAt φ p x →
      ∀ h : ℝ, h < h₀ → supportSection φ p x h ⊆ Metric.ball x r := by
  obtain ⟨δ, hδ, hgap⟩ := uniform_strict_supportResidual_sphere_gap hL hc hA hr
  refine ⟨δ, hδ, ?_⟩
  intro x hx p hp h hh y hy
  rw [Metric.mem_ball, dist_eq_norm]
  by_contra hfar
  have hdist : r ≤ ‖y - x‖ := le_of_not_gt hfar
  have hg := convex_ray_lower_bound (convexOn_supportResidual hc.convexOn p x)
    (supportResidual_self φ p x) hr (hgap x hx p hp) hdist
  have hlo := mul_le_mul_of_nonneg_left hdist hδ.le
  have hup := mul_le_mul_of_nonneg_left (show supportResidual φ p x y ≤ h from hy) hr.le
  have hlt := mul_lt_mul_of_pos_left hh hr
  nlinarith

/-- The actual height of a section through a nearby endpoint is at most
twice the global Lipschitz bound times the endpoint distance. -/
lemma supportResidual_le_lipschitz {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) {p x : E n} (hp : SupportsAt φ p x) (y : E n) :
    supportResidual φ p x y ≤ 2 * (L : ℝ) * ‖y - x‖ := by
  have hf := hL.norm_sub_le y x
  rw [Real.norm_eq_abs] at hf
  have hi := abs_real_inner_le_norm p (y - x)
  have hpL := supportsAt_norm_le hL hp
  have hm := mul_le_mul_of_nonneg_right hpL (norm_nonneg (y - x))
  have ha := le_abs_self (φ y - φ x)
  have hb := neg_le_abs (inner ℝ p (y - x))
  dsimp [supportResidual]
  nlinarith

/-- Unit-direction endpoints used in the oscillation contraction have a
uniformly small actual section height. -/
lemma supportResidual_line_height_le {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) {x v p : E n} {θ r : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hr : 0 ≤ r) (hv : ‖v‖ = 1)
    (hp : SupportsAt φ p (x + (θ * r / 4) • v)) :
    supportResidual φ p (x + (θ * r / 4) • v) (x + r • v) ≤ 2 * (L : ℝ) * r := by
  have hh := supportResidual_le_lipschitz hL hp (x + r • v)
  have he : (x + r • v) - (x + (θ * r / 4) • v) = (r - θ * r / 4) • v := by module
  have hsr : 0 ≤ r - θ * r / 4 := by
    have hm := mul_le_mul_of_nonneg_right hθ1 hr
    nlinarith
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsr, hv, mul_one] at hh
  have hle : r - θ * r / 4 ≤ r := by
    have hn : 0 ≤ θ * r / 4 := by positivity
    linarith
  exact hh.trans (mul_le_mul_of_nonneg_left hle (by positivity))

/-- A fixed local Alexandrov density pair controls every sufficiently small
section centered in a whole compact source neighborhood. -/
theorem uniform_section_balance_on_closedBall [NeZero n] {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : StrictConvexOn ℝ univ φ) (x₀ : E n)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam)
    (hmass : ∀ A : Set (E n), IsCompact A → A ⊆ Metric.closedBall x₀ 2 →
      ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ x ∈ Metric.closedBall x₀ 1, ∀ p,
      SupportsAt φ p x → ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ y ∈ supportSection φ p x h,
          x - sectionBalanceFactor n lam Lam • (y - x) ∈ supportSection φ p x h := by
  obtain ⟨h₀, hh₀, hsmall⟩ := uniform_small_supportSection_subset_ball hL hc
    (isCompact_closedBall x₀ 1) (r := 1) zero_lt_one
  refine ⟨h₀, hh₀, ?_⟩
  intro x hx p hp h hh hhsmall
  apply supportSection_reflection_balance hc.convexOn hp hh hlam hLam
    (isCompact_supportSection_of_strictConvexOn hc hp h)
  intro A hA hAS
  apply hmass A hA
  apply hAS.trans ((hsmall x hx p hp h hhsmall).trans ?_)
  apply Metric.ball_subset_closedBall.trans
  apply Metric.closedBall_subset_closedBall'
  have hxd : dist x x₀ ≤ 1 := hx
  linarith

/-- Genuine local contraction of directional supporting-slope oscillation,
with a positive radius uniform in the source center and unit direction.
Every geometric hypothesis is discharged from strict convexity and literal
local Alexandrov volume bounds. -/
theorem uniform_directional_support_contraction [NeZero n] {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : StrictConvexOn ℝ univ φ) (x₀ : E n)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam)
    (hmass : ∀ A : Set (E n), IsCompact A → A ⊆ Metric.closedBall x₀ 2 →
      ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    ∃ R : ℝ, 0 < R ∧ R ≤ 1 / 4 ∧ ∀ x ∈ Metric.closedBall x₀ (1 / 2),
      ∀ v : E n, ‖v‖ = 1 → ∀ r : ℝ, 0 < r → r ≤ R →
      ∀ p₀ p₁ p₂ p₃ : E n,
      SupportsAt φ p₀ (x + (-r) • v) →
      SupportsAt φ p₁ (x + (-(sectionBalanceFactor n lam Lam * r / 4)) • v) →
      SupportsAt φ p₂ (x + (sectionBalanceFactor n lam Lam * r / 4) • v) →
      SupportsAt φ p₃ (x + r • v) →
      inner ℝ (p₂ - p₁) v ≤
        (1 - sectionBalanceFactor n lam Lam / 8) * inner ℝ (p₃ - p₀) v := by
  obtain ⟨h₀, hh₀, hbalance⟩ := uniform_section_balance_on_closedBall hL hc x₀ hlam hLam hmass
  let θ := sectionBalanceFactor n lam Lam
  have hθ : 0 < θ := sectionBalanceFactor_pos hlam hLam
  have hθ1 : θ ≤ 1 := (sectionBalanceFactor_le_half n lam Lam).trans (by norm_num)
  let R := min (1 / 4) (h₀ / (2 * (L : ℝ) + 1)) / 2
  have hden : 0 < 2 * (L : ℝ) + 1 := by positivity
  have hR : 0 < R := half_pos (lt_min (by norm_num) (div_pos hh₀ hden))
  have hRquarter : R ≤ 1 / 4 := by
    have hh := min_le_left (1 / 4 : ℝ) (h₀ / (2 * (L : ℝ) + 1))
    dsimp [R]
    linarith
  have hRheight : 2 * (L : ℝ) * R < h₀ := by
    have hh := min_le_right (1 / 4 : ℝ) (h₀ / (2 * (L : ℝ) + 1))
    have hp : 0 < h₀ / (2 * (L : ℝ) + 1) := div_pos hh₀ hden
    have hlt : R < h₀ / (2 * (L : ℝ) + 1) := by dsimp [R]; linarith
    have hmul := (lt_div_iff₀ hden).mp hlt
    nlinarith
  refine ⟨R, hR, hRquarter, ?_⟩
  intro x hx v hv r hr hrR p₀ p₁ p₂ p₃ hp₀ hp₁ hp₂ hp₃
  have hv0 : v ≠ 0 := by intro he; simpa [he] using hv
  have hcenter : x + (θ * r / 4) • v ∈ Metric.closedBall x₀ 1 := by
    rw [Metric.mem_closedBall]
    have hd := dist_triangle (x + (θ * r / 4) • v) x x₀
    have hdsmall : dist (x + (θ * r / 4) • v) x = θ * r / 4 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), hv, mul_one]
    rw [hdsmall] at hd
    have hxd : dist x x₀ ≤ 1 / 2 := hx
    have hsr : θ * r / 4 ≤ r / 4 := by
      have hh := mul_le_mul_of_nonneg_right hθ1 hr.le
      nlinarith
    linarith
  apply directional_support_oscillation_contraction_of_balance hc hθ hθ1 hr hv0 hp₀ hp₁ hp₂ hp₃
  · exact (supportResidual_line_height_le hL hθ.le hθ1 hr.le hv hp₂).trans_lt
      ((mul_le_mul_of_nonneg_left hrR (by positivity : 0 ≤ 2 * (L : ℝ))).trans_lt hRheight)
  · exact hbalance _ hcenter p₂ hp₂

end GaussianTilt.MomentMapRegularity
