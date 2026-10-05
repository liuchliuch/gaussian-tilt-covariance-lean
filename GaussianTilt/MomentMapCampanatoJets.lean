import GaussianTilt.MomentMapCampanatoDifferentiation

/-! # Quantitative extraction of genuine quadratic jets

Polarization extracts the actual constant, linear and symmetric quadratic
coefficients from a uniform bound on a ball. These estimates make jet
coherence and Hessian interpolation consequences rather than assumptions.
-/
noncomputable section
open Set Filter
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma quadraticJet_even (a : ℝ) (p h : E n) (H : E n →L[ℝ] E n) :
    quadraticJet a p 0 H h + quadraticJet a p 0 H (-h) =
      2 * a + inner ℝ (H h) h := by
  simp only [quadraticJet, sub_zero, map_neg, inner_neg_left, inner_neg_right]
  ring

lemma quadraticJet_odd (a : ℝ) (p h : E n) (H : E n →L[ℝ] E n) :
    quadraticJet a p 0 H h - quadraticJet a p 0 H (-h) = 2 * inner ℝ p h := by
  simp only [quadraticJet, sub_zero, map_neg, inner_neg_left, inner_neg_right]
  ring

lemma quadraticJet_polarization (a : ℝ) (p v w : E n) (H : E n →L[ℝ] E n) (t : ℝ)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w)) :
    quadraticJet a p 0 H (t • (v + w)) + quadraticJet a p 0 H (-(t • (v + w))) -
      (quadraticJet a p 0 H (t • (v - w)) + quadraticJet a p 0 H (-(t • (v - w)))) =
        4 * t ^ 2 * inner ℝ (H v) w := by
  rw [quadraticJet_even, quadraticJet_even]
  simp only [map_smul, map_add, map_sub, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, conj_trivial]
  rw [hH w v, real_inner_comm w (H v)]
  ring

/-- Uniform size bounds determine the true quadratic coefficient, without
any differentiation or pre-existing coefficient estimate. -/
theorem quadraticJet_hessian_norm_bound (a : ℝ) (p : E n) (H : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w))
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hb : ∀ h : E n, ‖h‖ ≤ r → |quadraticJet a p 0 H h| ≤ ε) :
    ‖H‖ ≤ 4 * ε / r ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  rw [← innerSL_apply_norm ℝ (H v)]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  change |inner ℝ (H v) w| ≤ 4 * ε / r ^ 2
  have hplus : ‖(r / 2) • (v + w)‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    have h := norm_add_le v w
    rw [hv, hw] at h
    nlinarith
  have hminus : ‖(r / 2) • (v - w)‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    have h := norm_sub_le v w
    rw [hv, hw] at h
    nlinarith
  have h₁ := abs_le.mp (hb _ hplus)
  have h₂ := abs_le.mp (hb (-((r / 2) • (v + w))) (by simpa only [norm_neg] using hplus))
  have h₃ := abs_le.mp (hb _ hminus)
  have h₄ := abs_le.mp (hb (-((r / 2) • (v - w))) (by simpa only [norm_neg] using hminus))
  have he := quadraticJet_polarization a p v w H (r / 2) hH
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  rw [← abs_of_nonneg (sq_nonneg r), ← abs_mul]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The linear coefficient follows from the odd part of the polynomial. -/
theorem quadraticJet_gradient_norm_bound (a : ℝ) (p : E n) (H : E n →L[ℝ] E n)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hb : ∀ h : E n, ‖h‖ ≤ r → |quadraticJet a p 0 H h| ≤ ε) :
    ‖p‖ ≤ ε / r := by
  rw [← innerSL_apply_norm ℝ p]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  change |inner ℝ p v| ≤ ε / r
  have hh : ‖r • v‖ ≤ r := by simp [norm_smul, abs_of_pos hr, hv]
  have h₁ := abs_le.mp (hb _ hh)
  have h₂ := abs_le.mp (hb (-(r • v)) (by simpa only [norm_neg] using hh))
  have he := quadraticJet_odd a p (r • v) H
  rw [inner_smul_right] at he
  apply (le_div_iff₀ hr).mpr
  rw [← abs_of_pos hr, ← abs_mul, abs_le]
  constructor <;> nlinarith

lemma quadraticJet_constant_bound (a : ℝ) (p : E n) (H : E n →L[ℝ] E n)
    {r ε : ℝ} (hr : 0 ≤ r)
    (hb : ∀ h : E n, ‖h‖ ≤ r → |quadraticJet a p 0 H h| ≤ ε) : |a| ≤ ε := by
  simpa [quadraticJet] using hb 0 (by simpa using hr)

lemma quadraticJet_sub (a b : ℝ) (p q x : E n) (H K : E n →L[ℝ] E n) (h : E n) :
    quadraticJet a p x H h - quadraticJet b q x K h =
      quadraticJet (a - b) (p - q) x (H - K) h := by
  simp only [quadraticJet, inner_sub_left, ContinuousLinearMap.sub_apply]
  ring

/-- Two genuine quadratic approximations of the same function have close
coefficients. Thus jet coherence follows from approximation itself. -/
theorem quadraticJet_coherence {f : E n → ℝ}
    (a b : ℝ) (p q : E n) (H K : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w))
    (hK : ∀ v w, inner ℝ (K v) w = inner ℝ v (K w))
    {r ε η : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (ha : ∀ h : E n, ‖h‖ ≤ r → |f h - quadraticJet a p 0 H h| ≤ ε)
    (hb : ∀ h : E n, ‖h‖ ≤ r → |f h - quadraticJet b q 0 K h| ≤ η) :
    |a - b| ≤ ε + η ∧ ‖p - q‖ ≤ (ε + η) / r ∧ ‖H - K‖ ≤ 4 * (ε + η) / r ^ 2 := by
  have hc : ∀ h : E n, ‖h‖ ≤ r →
      |quadraticJet (a - b) (p - q) 0 (H - K) h| ≤ ε + η := by
    intro h hh
    rw [← quadraticJet_sub]
    calc
      |quadraticJet a p 0 H h - quadraticJet b q 0 K h| ≤
          |quadraticJet a p 0 H h - f h| + |f h - quadraticJet b q 0 K h| := abs_sub_le _ _ _
      _ ≤ ε + η := by rw [abs_sub_comm (quadraticJet a p 0 H h)]; exact add_le_add (ha h hh) (hb h hh)
  have hs : ∀ v w, inner ℝ ((H - K) v) w = inner ℝ v ((H - K) w) := by
    intro v w
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, hH, hK]
  exact ⟨quadraticJet_constant_bound _ _ _ hr.le hc,
    quadraticJet_gradient_norm_bound _ _ _ hr (add_nonneg hε hη) hc,
    quadraticJet_hessian_norm_bound _ _ _ hs hr (add_nonneg hε hη) hc⟩

end GaussianTilt.MomentMapRegularity
