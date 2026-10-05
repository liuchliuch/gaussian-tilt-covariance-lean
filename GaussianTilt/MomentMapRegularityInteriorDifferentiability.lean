import GaussianTilt.MomentMapRegularityInteriorBalance

/-!
# Differentiability from balanced actual sections

The geometric-to-analytic step is proved from the compact support graph.
A slope minimizing one directional projection has a sublinear supporting
error on the backward ray. Reflected section balance forces the forward
error to be sublinear as well, excluding every distinct supporting slope.
The balance premise below is an intermediate geometric input, supplied by
the actual normalized Aleksandrov estimates in the section-balance lane.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Local reflected balance of the actual positive-height sections excludes
multiple supporting slopes. The slope field need not be chosen continuously
and the potential need not be differentiable in advance. -/
theorem unique_support_of_local_section_balance {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (x : E n)
    (hbalance : ∀ p, SupportsAt φ p x → ∃ θ h₀ : ℝ,
      0 < θ ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ y ∈ supportSection φ p x h,
          x - θ • (y - x) ∈ supportSection φ p x h) :
    ∃ p, SupportsAt φ p x ∧ ∀ q, SupportsAt φ q x → q = p := by
  obtain ⟨p₀, hp₀⟩ := exists_supportsAt_of_lipschitz_convex hL hc x
  refine ⟨p₀, hp₀, ?_⟩
  intro q hq
  by_contra hne
  let v := q - p₀
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let P := subgradientImage φ {x}
  have hP : IsCompact P := isCompact_subgradientImage hL isCompact_singleton
  have hPne : P.Nonempty := ⟨p₀, x, mem_singleton x, hp₀⟩
  obtain ⟨p, hpP, hmin⟩ := hP.exists_isMinOn hPne
    (show Continuous (fun r : E n => inner ℝ r v) from continuous_id.inner continuous_const).continuousOn
  obtain ⟨z, hz, hp⟩ := hpP
  have hzx : z = x := mem_singleton_iff.mp hz
  subst z
  have hmin₀ : inner ℝ p v ≤ inner ℝ p₀ v := hmin ⟨x, mem_singleton x, hp₀⟩
  let d := inner ℝ (q - p) v
  have hd : 0 < d := by
    have he : inner ℝ (q - p₀) v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    dsimp [d]
    rw [inner_sub_left] at he ⊢
    nlinarith [sq_pos_of_pos hv]
  obtain ⟨θ, h₀, hθ, hh₀, hbal⟩ := hbalance p hp
  let ε := θ * d / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  let U := {r : E n | inner ℝ p v - ε < inner ℝ r v}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_id.inner continuous_const)
  have hPU : ∀ r, SupportsAt φ r x → r ∈ U := by
    intro r hr
    have hle : inner ℝ p v ≤ inner ℝ r v := hmin ⟨x, mem_singleton x, hr⟩
    change inner ℝ p v - ε < inner ℝ r v
    linarith
  have hnear := eventually_supportsAt_mem_open hL hU hPU
  have htend : Tendsto (fun t : ℝ => x - t • v) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℝ => x - t • v) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    simpa using hcont.tendsto (0 : ℝ)
  obtain ⟨η, hη, hηnear⟩ := Metric.eventually_nhds_iff.mp (htend.eventually hnear)
  let t := min η (h₀ / (2 * ε)) / 2
  have ht : 0 < t := by dsimp [t]; exact half_pos (lt_min hη (div_pos hh₀ (by positivity)))
  have htη : t < η := by
    have hm := min_le_left η (h₀ / (2 * ε))
    dsimp [t]
    linarith
  have hth : 2 * ε * t < h₀ := by
    have hm := min_le_right η (h₀ / (2 * ε))
    have hdiv : 0 < h₀ / (2 * ε) := div_pos hh₀ (by positivity)
    have hlt : t < h₀ / (2 * ε) := by dsimp [t]; linarith
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * ε)).mp hlt
    nlinarith
  let y := x - t • v
  obtain ⟨r, hr⟩ := exists_supportsAt_of_lipschitz_convex hL hc y
  have hrU : inner ℝ p v - ε < inner ℝ r v := by
    have hdist : dist t 0 < η := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htη
    exact hηnear hdist r hr
  have hres : supportResidual φ p x y ≤ ε * t := by
    have hrs := hr x
    have hxy : x - y = t • v := by dsimp [y]; module
    have hyx : y - x = -(t • v) := by dsimp [y]; module
    rw [hxy, inner_smul_right] at hrs
    dsimp [supportResidual]
    rw [hyx, inner_neg_right, inner_smul_right]
    have hm := mul_lt_mul_of_pos_left hrU ht
    nlinarith
  have hyS : y ∈ supportSection φ p x (2 * ε * t) := by
    change supportResidual φ p x y ≤ 2 * ε * t
    nlinarith [mul_pos hε ht]
  have hwS := hbal (2 * ε * t) (by positivity) hth y hyS
  let w := x - θ • (y - x)
  have hwx : w - x = (θ * t) • v := by dsimp [w, y]; module
  have hforward : θ * t * d ≤ supportResidual φ p x w := by
    have hqs := hq w
    rw [hwx, inner_smul_right] at hqs
    dsimp [supportResidual]
    rw [hwx, inner_smul_right]
    dsimp [d]
    rw [inner_sub_left]
    nlinarith
  have hu : supportResidual φ p x w ≤ 2 * ε * t := hwS
  have hpos : 0 < θ * t * d := mul_pos (mul_pos hθ ht) hd
  dsimp [ε] at hu
  nlinarith

/-- Section balance yields actual Fréchet differentiability, via the
proved singleton-support criterion. -/
theorem differentiableAt_of_local_section_balance {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (x : E n)
    (hbalance : ∀ p, SupportsAt φ p x → ∃ θ h₀ : ℝ,
      0 < θ ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ y ∈ supportSection φ p x h,
          x - θ • (y - x) ∈ supportSection φ p x h) :
    DifferentiableAt ℝ φ x :=
  (differentiableAt_iff_unique_support hL hc x).mpr
    (unique_support_of_local_section_balance hL hc x hbalance)

end GaussianTilt.MomentMapRegularity
