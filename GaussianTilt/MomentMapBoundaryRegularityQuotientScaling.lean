import GaussianTilt.MomentMapBoundaryRegularityQuotientOscillation

/-! # Exact scale covariance of the literal boundary quotient -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma boundaryQuotientValues_rescale (u : CoordinateSpace n → ℝ) (j : Fin n)
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    boundaryQuotientValues (flatRescaledSolution u r) j s = boundaryQuotientValues u j (r*s) := by
  ext q
  constructor
  · rintro ⟨x,hx,hj,hq⟩
    refine ⟨r • x,?_,?_,?_⟩
    · rw [norm_coordinate_dilation,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hx hr.le
    · change 0 < r*x j
      exact mul_pos hr hj
    · change u (r • x)/(r*x j)=q
      rw [← hq]
      dsimp [flatRescaledSolution]
      field_simp
  · rintro ⟨y,hy,hj,hq⟩
    let x := r⁻¹ • y
    have hxy : r • x=y := by simp [x,smul_smul,hr.ne']
    have hxj : 0 < x j := by change 0 < r⁻¹*y j; positivity
    refine ⟨x,?_,hxj,?_⟩
    · rw [norm_coordinate_dilation,abs_of_pos (inv_pos.mpr hr)]
      have hh := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hr.le)
      calc
        _ ≤ r⁻¹*(r*s) := hh
        _ = s := by field_simp
    · dsimp [flatRescaledSolution]
      rw [hxy]
      change r⁻¹*u y/(r⁻¹*y j)=q
      rw [← hq]
      field_simp

lemma boundaryQuotientOscillation_rescale (u : CoordinateSpace n → ℝ) (j : Fin n)
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    boundaryQuotientOscillation (flatRescaledSolution u r) j s = boundaryQuotientOscillation u j (r*s) := by
  simp only [boundaryQuotientOscillation,boundaryQuotientValues_rescale u j hr s]

lemma flatRescaledSolution_quotient_bound {u : CoordinateSpace n → ℝ} {j : Fin n} {B r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) :
    ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |flatRescaledSolution u r x| ≤ B*x j := by
  intro x hx hj
  have hnorm : ‖(coordinateEquiv n).symm (r • x)‖ ≤ 1 := by
    rw [norm_coordinate_dilation,abs_of_pos hr]
    nlinarith
  have hheight : 0 ≤ (r • x) j := by change 0 ≤ r*x j; positivity
  have hh := mul_le_mul_of_nonneg_left (hb (r • x) hnorm hheight) (inv_nonneg.mpr hr.le)
  change r⁻¹*|u (r • x)| ≤ r⁻¹*(B*(r*x j)) at hh
  have he : r⁻¹*(B*(r*x j))=B*x j := by field_simp
  rw [he] at hh
  simpa only [flatRescaledSolution,abs_mul,abs_of_pos (inv_pos.mpr hr)] using hh

end GaussianTilt.MomentMapRegularity
