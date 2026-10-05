import GaussianTilt.MomentMapRegularityImprovementDensity
import GaussianTilt.MomentMapRegularityImprovementDistortion

/-! # Exact composition of source normalizations and their actual density -/
noncomputable section
open Set InnerProductSpace
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The new supporting affine coefficient is transported contragrediently
through the actual preceding source-coordinate map. -/
def improvementPlaneUpdate (P : E n ≃L[ℝ] E n) (R : ℝ) (b p : E n) : E n :=
  b+R • (P.symm.toLinearEquiv.toLinearMap.adjoint p)

lemma improvementRescale_comp (u : E n → ℝ) (b p : E n)
    (P L : E n ≃L[ℝ] E n) {R ρ : ℝ} (hR : R≠0) (hρ : ρ≠0) :
    improvementRescale (improvementRescale u b P R) p L ρ =
      improvementRescale u (improvementPlaneUpdate P R b p) (L.trans P) (R*ρ) := by
  funext x
  have hpair : inner ℝ (P.symm.toLinearEquiv.toLinearMap.adjoint p) (P (L x)) = inner ℝ p (L x) := by
    rw [LinearMap.adjoint_inner_left]
    simp
  have htrans (y : E n) : (L.trans P : E n →L[ℝ] E n) y=P (L y) := rfl
  have hpoint : R • P (ρ • L x)=(R*ρ) • (L.trans P) x := by simp [smul_smul]
  simp only [improvementRescale,improvementRescale_zero,map_zero,smul_zero,inner_zero_right,
    sub_zero,improvementPlaneUpdate,inner_add_left,real_inner_smul_left,map_smul,
    real_inner_smul_right,ContinuousLinearEquiv.trans_apply,htrans,smul_smul,hpair]
  simp only [ContinuousLinearEquiv.coe_apply]
  field_simp
  ring

/-- The actual density oscillation after a finite affine normalization is
controlled by the proved norm of that map and the physical scale. -/
lemma density_oscillation_after_normalization {f : E n → ℝ} {α F r D S : ℝ}
    (hα : 0≤α) (hF : 0≤F) (hr : 0≤r) (hD : 0≤D) (hS : 0≤S)
    (P : E n →L[ℝ] E n) (hP : ‖P‖≤D)
    (hf : ∀ y, |f y-1|≤F*‖y‖^α) :
    ∀ x, ‖x‖≤S → |f (r • P x)-1|≤F*(r*D*S)^α := by
  intro x hx
  apply (hf _).trans
  apply mul_le_mul_of_nonneg_left _ hF
  apply Real.rpow_le_rpow (norm_nonneg _) _ hα
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  have hpx : ‖P x‖≤D*S := (P.le_opNorm x).trans
    ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hx hD))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpx hr

end GaussianTilt.MomentMapRegularity
