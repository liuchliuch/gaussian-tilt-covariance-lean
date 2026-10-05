import GaussianTilt.MomentMapRegularityImprovementComposition

/-! # Keeping the genuine reference Taylor remainder at physical radii -/
noncomputable section
open Set InnerProductSpace
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def physicalQuadraticHessian (P : E n ≃L[ℝ] E n) (H : E n →L[ℝ] E n) : E n →L[ℝ] E n :=
  (P.symm : E n →L[ℝ] E n).adjoint.comp (H.comp (P.symm : E n →L[ℝ] E n))

def physicalQuadraticGradient (P : E n ≃L[ℝ] E n) (R : ℝ) (b p : E n) : E n :=
  b+R • (P.symm : E n →L[ℝ] E n).adjoint p

lemma physicalQuadraticHessian_symmetric (P : E n ≃L[ℝ] E n) {H : E n →L[ℝ] E n}
    (hH : ∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) :
    ∀ v w, inner ℝ (physicalQuadraticHessian P H v) w=
      inner ℝ v (physicalQuadraticHessian P H w) := by
  intro v w
  simp only [physicalQuadraticHessian,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_right]
  exact hH _ _

lemma quadraticJet_physical_rescaling (U : E n → ℝ) (b p : E n)
    (P : E n ≃L[ℝ] E n) (H : E n →L[ℝ] E n) (a R : ℝ) (hR : R≠0) (x : E n) :
    U x-quadraticJet (U 0+R^2*a) (physicalQuadraticGradient P R b p) 0 (physicalQuadraticHessian P H) x =
      R^2*(improvementRescale U b P R (R⁻¹ • P.symm x)-quadraticJet a p 0 H (R⁻¹ • P.symm x)) := by
  have he : R • (P : E n →L[ℝ] E n) (R⁻¹ • P.symm x)=x := by simp [smul_smul,hR]
  simp only [improvementRescale,he,quadraticJet,sub_zero,physicalQuadraticGradient,
    physicalQuadraticHessian,inner_add_left,real_inner_smul_left,real_inner_smul_right,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,map_smul,
    ContinuousLinearEquiv.coe_apply]
  simp only [P.apply_symm_apply,smul_smul,mul_inv_cancel₀ hR,one_smul]
  field_simp
  ring

/-- This preserves the actual cubic dependence on the physical displacement.
It avoids losing the positive remainder order in gaps between adaptive scales. -/
theorem physical_quadratic_remainder_of_reference {U v : E n → ℝ} {b p : E n}
    (P : E n ≃L[ℝ] E n) {H : E n →L[ℝ] E n} {a R D ε C s : ℝ}
    (hR : 0 < R) (hD : 0≤D) (hε : 0≤ε) (hC : 0≤C)
    (hP : ‖(P.symm : E n →L[ℝ] E n)‖≤D)
    (hcompare : ∀ y, ‖y‖≤s → |improvementRescale U b P R y-v y|≤ε)
    (hTaylor : ∀ y, ‖y‖≤s → |v y-quadraticJet a p 0 H y|≤C*‖y‖^3) :
    ∀ x, D*‖x‖≤R*s →
      |U x-quadraticJet (U 0+R^2*a) (physicalQuadraticGradient P R b p) 0 (physicalQuadraticHessian P H) x|≤
        R^2*ε+C*D^3*‖x‖^3/R := by
  intro x hx
  let y := R⁻¹ • P.symm x
  have hybound : ‖y‖≤D*‖x‖/R := by
    rw [show y=R⁻¹ • P.symm x from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    have hh := ((P.symm : E n →L[ℝ] E n).le_opNorm x).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hR.le)
  have hy : ‖y‖≤s := hybound.trans ((div_le_iff₀ hR).mpr (by linarith))
  have herr : |improvementRescale U b P R y-quadraticJet a p 0 H y|≤ε+C*(D*‖x‖/R)^3 := by
    apply (abs_sub_le _ (v y) _).trans
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hybound 3) hC
    linarith [hcompare y hy,hTaylor y hy]
  rw [quadraticJet_physical_rescaling U b p P H a R hR.ne' x,abs_mul,abs_of_nonneg (sq_nonneg R)]
  have hh := mul_le_mul_of_nonneg_left herr (sq_nonneg R)
  convert hh using 1 <;> field_simp <;> ring

end GaussianTilt.MomentMapRegularity
