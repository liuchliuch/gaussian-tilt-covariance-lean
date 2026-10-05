import GaussianTilt.MomentMapCampanatoJets
import GaussianTilt.MomentMapRegularityImprovementGeometry

/-! # Actual coefficient control in the quadratic improvement step

A reference close in value to the unit quadratic, with its derived cubic
Taylor remainder, has an actual Hessian close to the identity. The estimate
is proved by finite quadratic coefficient extraction.
-/
noncomputable section
open Set
open scoped Topology
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma quadraticJet_sub_unit (a : ℝ) (p : E n) (H : E n →L[ℝ] E n) (x : E n) :
    quadraticJet a p 0 (H-ContinuousLinearMap.id ℝ (E n)) x =
      quadraticJet a p 0 H x-‖x‖^2/2 := by
  simp only [quadraticJet,sub_zero,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply,inner_sub_left,real_inner_self_eq_norm_sq]
  ring

lemma symmetric_sub_identity {H : E n →L[ℝ] E n}
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w)) :
    ∀ v w, inner ℝ ((H-ContinuousLinearMap.id ℝ (E n)) v) w =
      inner ℝ v ((H-ContinuousLinearMap.id ℝ (E n)) w) := by
  intro v w
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    inner_sub_left,inner_sub_right,hH]

/-- Quantitative Hessian and gradient coefficient proximity, derived from
uniform value error and an actual cubic Taylor remainder. -/
theorem quadratic_coefficients_near_identity {v : E n → ℝ} {a : ℝ} {p : E n}
    {H : E n →L[ℝ] E n} (hH : ∀ z w, inner ℝ (H z) w = inner ℝ z (H w))
    {R r ε C : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (happrox : ∀ h : E n, ‖h‖ ≤ R → |v h-‖h‖^2/2| ≤ ε)
    (hTaylor : ∀ h : E n, ‖h‖ ≤ R → |v h-quadraticJet a p 0 H h| ≤ C*‖h‖^3) :
    ‖H-ContinuousLinearMap.id ℝ (E n)‖ ≤ 4*ε/r^2+4*C*r ∧
      ‖p‖ ≤ ε/r+C*r^2 := by
  have hb : ∀ h : E n, ‖h‖ ≤ r →
      |quadraticJet a p 0 (H-ContinuousLinearMap.id ℝ (E n)) h| ≤ ε+C*r^3 := by
    intro h hh
    rw [quadraticJet_sub_unit]
    calc
      _ ≤ |quadraticJet a p 0 H h-v h|+|v h-‖h‖^2/2| := abs_sub_le _ _ _
      _ ≤ C*‖h‖^3+ε := add_le_add
        (by simpa only [abs_sub_comm] using hTaylor h (hh.trans hrR)) (happrox h (hh.trans hrR))
      _ ≤ ε+C*r^3 := by
        have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg h) hh 3) hC
        linarith
  have he : 0 ≤ ε+C*r^3 := by positivity
  have h1 := quadraticJet_hessian_norm_bound a p (H-ContinuousLinearMap.id ℝ (E n))
    (symmetric_sub_identity hH) hr he hb
  have h2 := quadraticJet_gradient_norm_bound a p (H-ContinuousLinearMap.id ℝ (E n)) hr he hb
  constructor
  · convert h1 using 1 <;> field_simp <;> ring
  · convert h2 using 1 <;> field_simp <;> ring

/-- The inner near-quadratic inclusion has a strict value margin, hence the
whole closed inner ball lies in the actual section interior. -/
lemma near_quadratic_section_contains_closedBall_interior {u : E n → ℝ}
    (hu : Continuous u) {R ρ η ε : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hη1 : η < 1)
    (houter : ρ*(1+η) ≤ R) (hε : ε ≤ η*ρ^2/2)
    (happrox : ∀ x : E n, ‖x‖ ≤ R → |u x-‖x‖^2/2| ≤ ε) :
    Metric.closedBall (0 : E n) (ρ*(1-η)) ⊆ interior {x | u x ≤ ρ^2/2} := by
  intro x hx
  have hin : 0 < ρ*(1-η) := mul_pos hρ (sub_pos.mpr hη1)
  have hnorm : ‖x‖ ≤ ρ*(1-η) := by simpa using hx
  have hnormR : ‖x‖ ≤ R := hnorm.trans ((by nlinarith : ρ*(1-η) ≤ ρ*(1+η)).trans houter)
  have hsq : ‖x‖^2 ≤ (ρ*(1-η))^2 := (sq_le_sq₀ (norm_nonneg _) hin.le).mpr hnorm
  have hh := (abs_le.mp (happrox x hnormR)).2
  have hp : 0 < ρ^2*(η-η^2) := mul_pos (sq_pos_of_pos hρ) (by nlinarith)
  have hlt : u x < ρ^2/2 := by nlinarith
  exact interior_maximal (fun y hy => show u y ≤ ρ^2/2 from le_of_lt hy)
    (isOpen_lt hu continuous_const) hlt

end GaussianTilt.MomentMapRegularity
