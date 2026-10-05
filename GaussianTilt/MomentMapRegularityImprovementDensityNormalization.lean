import GaussianTilt.MomentMapRegularityImprovementDensity
import GaussianTilt.MomentMapRegularityImprovementCoordinateBounds

/-! # Exact normalization of the central Alexandrov density -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def densityNormalizationFactor (n : ℕ) (d : ℝ) : ℝ := (d⁻¹)^((n:ℝ)⁻¹)

lemma densityNormalizationFactor_pos {d : ℝ} (hd : 0 < d) : 0 < densityNormalizationFactor n d :=
  Real.rpow_pos_of_pos (inv_pos.mpr hd) _

lemma densityNormalizationFactor_power [NeZero n] {d : ℝ} (hd : 0 < d) :
    (densityNormalizationFactor n d)^n=d⁻¹ := Real.rpow_inv_natCast_pow (inv_nonneg.mpr hd.le) (NeZero.ne n)

/-- After the actual affine coordinate map and an explicit positive
amplitude normalization, the density is precisely f(T⁻¹y+a)/f(a). -/
theorem alexandrov_density_center_normalized [NeZero n] {u f : E n → ℝ}
    (T : E n ≃L[ℝ] E n) (a p : E n) (b : ℝ) (hf : 0 < f a)
    {A : Set (E n)} (hA : IsCompact A)
    (hMA : volume (subgradientImage u (affineSource T a '' A))=
      ∫⁻ y in affineSource T a '' A, ENNReal.ofReal (f y)) :
    volume (subgradientImage (fun y=>
      densityNormalizationFactor n (|(T.symm : E n →L[ℝ] E n).det|^2*f a)*affinePotential u T a p b y) A)=
      ∫⁻ y in A, ENNReal.ofReal (f (affineSource T a y)/f a) := by
  have hd : 0 < |(T.symm : E n →L[ℝ] E n).det|^2 :=
    sq_pos_of_pos (abs_pos.mpr T.symm.toLinearEquiv.isUnit_det'.ne_zero)
  have hdf : 0 < |(T.symm : E n →L[ℝ] E n).det|^2*f a := mul_pos hd hf
  rw [alexandrov_density_affine_vertical T a p b (densityNormalizationFactor_pos hdf) hA hMA]
  apply lintegral_congr
  intro y
  rw [densityNormalizationFactor_power hdf]
  congr 1
  have hdetabs : |(T.symm : E n →L[ℝ] E n).det|≠0 := abs_ne_zero.mpr T.symm.toLinearEquiv.isUnit_det'.ne_zero
  field_simp [hdetabs]

/-- Relative Hölder oscillation is made small by the true inverse affine
coordinate norm, not by an assumed well-shaped source Hessian. -/
lemma normalized_density_holder {f : E n → ℝ} (T : E n ≃L[ℝ] E n) (a : E n)
    {α F M m : ℝ} (hα : 0≤α) (hF : 0≤F) (hM : 0≤M) (hm : 0 < m)
    (hfm : m≤f a) (hT : ‖(T.symm : E n →L[ℝ] E n)‖≤M)
    (hf : ∀ y, |f (affineSource T a y)-f a|≤F*‖T.symm y‖^α) :
    ∀ y, |f (affineSource T a y)/f a-1|≤(F*M^α/m)*‖y‖^α := by
  have hfa : 0 < f a := hm.trans_le hfm
  intro y
  have he : f (affineSource T a y)/f a-1=(f (affineSource T a y)-f a)/f a := by field_simp
  rw [he,abs_div,abs_of_pos hfa]
  have hnorm := ((T.symm : E n →L[ℝ] E n).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hpower := Real.rpow_le_rpow (norm_nonneg (T.symm y)) hnorm hα
  have hbound := (hf y).trans (mul_le_mul_of_nonneg_left hpower hF)
  have hh := (div_le_div_of_nonneg_right hbound hfa.le).trans
    (div_le_div_of_nonneg_left (by positivity) hm hfm)
  rw [Real.mul_rpow hM (norm_nonneg _)] at hh
  convert hh using 1 <;> ring

end GaussianTilt.MomentMapRegularity
