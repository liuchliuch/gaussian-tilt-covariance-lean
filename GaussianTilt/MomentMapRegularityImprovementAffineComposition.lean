import GaussianTilt.MomentMapRegularityImprovementAffineJets

/-! # Exact combined coordinates of density and reference source normalization -/
noncomputable section
open Set InnerProductSpace
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def rescaleAffineCoordinate (T L : E n ≃L[ℝ] E n) {σ : ℝ} (hσ : σ≠0) : E n ≃L[ℝ] E n :=
  (improvementCoordinateMap (L.trans T.symm) hσ).symm

def rescaleAffinePlane (T : E n ≃L[ℝ] E n) (t : ℝ) (p q : E n) : E n :=
  p+t⁻¹ • T.toLinearEquiv.toLinearMap.adjoint q

lemma rescaleAffineCoordinate_symm_apply (T L : E n ≃L[ℝ] E n) {σ : ℝ}
    (hσ : σ≠0) (y : E n) : (rescaleAffineCoordinate T L hσ).symm y=σ • T.symm (L y) := by
  simp [rescaleAffineCoordinate,improvementCoordinateMap_apply]

lemma rescaleAffineCoordinate_apply (T L : E n ≃L[ℝ] E n) {σ : ℝ}
    (hσ : σ≠0) (y : E n) : rescaleAffineCoordinate T L hσ y=σ⁻¹ • L.symm (T y) := by
  apply (rescaleAffineCoordinate T L hσ).symm.injective
  rw [(rescaleAffineCoordinate T L hσ).symm_apply_apply,rescaleAffineCoordinate_symm_apply]
  simp [smul_smul,hσ]

lemma improvementRescale_affine_vertical (φ : E n → ℝ) (T L : E n ≃L[ℝ] E n)
    (x p q : E n) (b t : ℝ) (ht : t≠0) {σ : ℝ} (hσ : σ≠0) :
    improvementRescale (fun y=>t*affinePotential φ T x p b y) q L σ=
      fun y=>(t/σ^2)*affinePotential φ (rescaleAffineCoordinate T L hσ) x
        (rescaleAffinePlane T t p q) (φ x-inner ℝ (rescaleAffinePlane T t p q) x) y := by
  funext y
  have hid : affineSource (rescaleAffineCoordinate T L hσ) x y=affineSource T x (σ • L y) := by
    simp [affineSource,rescaleAffineCoordinate_symm_apply]
  have hpair : inner ℝ (T.toLinearEquiv.toLinearMap.adjoint q) (T.symm (σ • L y))=
      inner ℝ q (σ • L y) := by rw [LinearMap.adjoint_inner_left]; simp
  simp only [improvementRescale,affinePotential,hid]
  simp only [affineSource,map_zero,smul_zero,zero_add,
    rescaleAffinePlane,inner_add_left,real_inner_smul_left,inner_add_right,
    ContinuousLinearEquiv.coe_apply,hpair]
  field_simp
  ring

/-- The final physical-to-normalized coordinate norm follows from the two
actual affine factors and the chosen reference scale. -/
lemma rescaleAffineCoordinate_norm_bound (T L : E n ≃L[ℝ] E n) {σ : ℝ}
    (hσ : 0 < σ) {B M : ℝ} (hB : 0≤B) (hM : 0≤M)
    (hT : ‖(T : E n →L[ℝ] E n)‖≤B) (hL : ‖(L.symm : E n →L[ℝ] E n)‖≤M) :
    ‖(rescaleAffineCoordinate T L hσ.ne' : E n →L[ℝ] E n)‖≤σ⁻¹*M*B := by
  have he : (rescaleAffineCoordinate T L hσ.ne' : E n →L[ℝ] E n)=
      σ⁻¹ • ((L.symm : E n →L[ℝ] E n).comp (T : E n →L[ℝ] E n)) := by
    apply ContinuousLinearMap.ext
    intro y
    exact rescaleAffineCoordinate_apply T L hσ.ne' y
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hσ)]
  have hh := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hL hT (norm_nonneg _) hM)
  have hm := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hσ).le
  simpa only [mul_assoc] using hm

end GaussianTilt.MomentMapRegularity
