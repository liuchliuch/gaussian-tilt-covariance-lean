import GaussianTilt.MomentMapClassicalDirichletBoundaryBounds

/-! # Boundary estimates on the actually constructed smooth domains -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Zero boundary data and the actual scaled barriers supply all first
boundary jets and the full tangential second jet. -/
theorem boundary_jet_data {u : E n → ℝ} {a b : ℝ} {x : E n}
    (hx : x ∈ frontier d.domain) (hu : ContDiffAt ℝ 2 u x)
    (hzero : ∀ y ∈ frontier d.domain, u y = 0)
    (hbar : ∀ y ∈ d.body, b*d.defining y ≤ u y ∧ u y ≤ a*d.defining y) :
    ∃ lam : ℝ, a ≤ lam ∧ lam ≤ b ∧
      fderiv ℝ u x = lam • fderiv ℝ d.defining x ∧
      gradient u x = lam • gradient d.defining x ∧
      ∀ v z : E n, fderiv ℝ d.defining x v = 0 → fderiv ℝ d.defining x z = 0 →
        fderiv ℝ (fderiv ℝ u) x v z = lam * fderiv ℝ (fderiv ℝ d.defining) x v z := by
  have hwx : d.defining x = 0 := by rwa [d.frontier_domain] at hx
  have hw : ContDiffAt ℝ 2 d.defining x := (contDiff_infty.mp d.smooth 2).contDiffAt
  obtain ⟨e,he⟩ := exists_unit_transverse (d.regular_level x hwx)
  have hlevel : ∀ᶠ y in 𝓝 x, d.defining y = d.defining x → u y = u x := by
    apply Eventually.of_forall
    intro y hy
    have hyb : y ∈ frontier d.domain := by rw [d.frontier_domain]; exact hy.trans hwx
    rw [hzero y hyb, hzero x hx]
  have hbounds := normal_multiplier_bounds_of_barriers (hu.differentiableAt (by norm_num))
    (hw.differentiableAt (by norm_num)) he (hzero x hx) hwx
    (Eventually.of_forall (fun y hy => hbar y (show d.defining y ≤ 0 from hy.le)))
  have hfirst := fderiv_eq_smul_of_level_constant (hu.differentiableAt (by norm_num)) hw he hlevel
  exact ⟨fderiv ℝ u x e, hbounds.1, hbounds.2, hfirst,
    gradient_eq_smul_of_fderiv_eq_smul hfirst, fun v z hv hz =>
      secondFDeriv_tangent_bilinear_eq_of_level_constant hu hw he hv hz hlevel⟩

lemma hessian_norm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ d.body, ∀ v z : E n,
    |fderiv ℝ (fderiv ℝ d.defining) x v z| ≤ C * ‖v‖ * ‖z‖ := by
  have hD : ContDiff ℝ 1 (fderiv ℝ d.defining) :=
    (contDiff_infty.mp d.smooth 2).fderiv_right (by norm_num)
  obtain ⟨C,hC⟩ := d.compact_sublevel.exists_bound_of_continuousOn
    (hD.continuous_fderiv le_rfl).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx v z
  calc
    _ = ‖fderiv ℝ (fderiv ℝ d.defining) x v z‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (fderiv ℝ d.defining) x v‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ d.defining) x‖ * ‖v‖) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (max C 0 * ‖v‖) * ‖z‖ := by
      gcongr
      exact (hC x hx).trans (le_max_left _ _)

/-- Uniform tangential ellipticity and upper bounds follow from the scaled
barriers. No boundary Hessian estimate is inserted as a premise. -/
theorem boundary_tangential_hessian_bounds {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : E n → ℝ) (x : E n), x ∈ frontier d.domain →
      ContDiffAt ℝ 2 u x → (∀ y ∈ frontier d.domain, u y = 0) →
      (∀ y ∈ d.body, b*d.defining y ≤ u y ∧ u y ≤ a*d.defining y) →
      (∀ v, fderiv ℝ d.defining x v = 0 →
        (a*d.modulus)*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ u) x v v) ∧
      (∀ v z, fderiv ℝ d.defining x v = 0 → fderiv ℝ d.defining x z = 0 →
        |fderiv ℝ (fderiv ℝ u) x v z| ≤ b*C*‖v‖*‖z‖) := by
  obtain ⟨C,hC,hH⟩ := d.hessian_norm_bound
  refine ⟨C,hC,?_⟩
  intro u x hx hu hzero hbar
  obtain ⟨lam,hla,hlb,hfirst,hgrad,hsecond⟩ := d.boundary_jet_data hx hu hzero hbar
  have hlam : 0 ≤ lam := ha.le.trans hla
  have hxb : x ∈ d.body := by rw [← d.closure_domain]; exact frontier_subset_closure hx
  constructor
  · intro v hv
    rw [hsecond v v hv hv]
    have hh := d.hessian_lower x v
    have h1 := mul_le_mul_of_nonneg_left hh hlam
    have h2 := mul_le_mul_of_nonneg_right hla (mul_nonneg d.modulus_pos.le (sq_nonneg ‖v‖))
    nlinarith
  · intro v z hv hz
    rw [hsecond v z hv hz, abs_mul, abs_of_nonneg hlam]
    calc
      _ ≤ lam*(C*‖v‖*‖z‖) := mul_le_mul_of_nonneg_left (hH x hxb v z) hlam
      _ ≤ b*(C*‖v‖*‖z‖) := mul_le_mul_of_nonneg_right hlb (by positivity)
      _ = _ := by ring

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
