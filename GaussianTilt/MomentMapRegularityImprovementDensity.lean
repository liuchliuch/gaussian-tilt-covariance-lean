import GaussianTilt.MomentMapRegularityImprovementRescaling
import GaussianTilt.MomentMapRegularityLocalizationAffine
import GaussianTilt.MomentMapRegularitySecondOrderComparison

/-! # Literal Alexandrov density under quadratic source rescaling -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Both changes of volume are accounted for, including the vertical
homogeneity of the actual supporting-plane image. -/
theorem alexandrov_density_affine_vertical {u f : E n → ℝ}
    (T : E n ≃L[ℝ] E n) (a p : E n) (b : ℝ) {t : ℝ} (ht : 0 < t)
    {A : Set (E n)} (hA : IsCompact A)
    (hMA : volume (subgradientImage u (affineSource T a '' A)) =
      ∫⁻ y in affineSource T a '' A, ENNReal.ofReal (f y)) :
    volume (subgradientImage (fun y => t*affinePotential u T a p b y) A) =
      ∫⁻ y in A, ENNReal.ofReal (t^n * |(T.symm : E n →L[ℝ] E n).det|^2 *
        f (affineSource T a y)) := by
  have hid : volume (subgradientImage (fun y => t*affinePotential u T a p b y) A) =
      ENNReal.ofReal (t^n)* ENNReal.ofReal |(T.symm : E n →L[ℝ] E n).det| *
      ∫⁻ y in affineSource T a '' A, ENNReal.ofReal (f y) := by
    have hh := volume_subgradientImage_pos_mul_add_const (affinePotential u T a p b) ht 0 A
    simp only [add_zero] at hh
    rw [hh,volume_subgradientImage_affine,hMA]
    exact (mul_assoc _ _ _).symm
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA.measurableSet
    (fun y _ => ((T.symm : E n →L[ℝ] E n).hasFDerivAt.add_const a).hasFDerivWithinAt)
    (show InjOn (affineSource T a) A from fun x _ y _ h => T.symm.injective (add_right_cancel h))
    (fun y => ENNReal.ofReal (f y))
  change (∫⁻ y in affineSource T a '' A, ENNReal.ofReal (f y)) =
    ∫⁻ y in A, ENNReal.ofReal |(T.symm : E n →L[ℝ] E n).det| * ENNReal.ofReal (f (affineSource T a y)) at hj
  rw [hid,hj]
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg ht.le _) (sq_nonneg _)),
    ENNReal.ofReal_mul (pow_nonneg ht.le _),ENNReal.ofReal_pow (abs_nonneg _)]
  ring

/-- Scalar dilation composed with the actual Hessian normalization. -/
def improvementCoordinateMap (L : E n ≃L[ℝ] E n) {ρ : ℝ} (hρ : ρ ≠ 0) : E n ≃L[ℝ] E n :=
  L.trans (ContinuousLinearEquiv.smulLeft (R₁:=ℝ) (M₁:=E n) (Units.mk0 ρ hρ))

@[simp] lemma improvementCoordinateMap_apply (L : E n ≃L[ℝ] E n) {ρ : ℝ}
    (hρ : ρ ≠ 0) (x : E n) : improvementCoordinateMap L hρ x = ρ • L x := rfl

lemma improvementCoordinateMap_det (L : E n ≃L[ℝ] E n) {ρ : ℝ} (hρ : ρ ≠ 0) :
    (improvementCoordinateMap L hρ : E n →L[ℝ] E n).det =
      ρ^n*(L : E n →L[ℝ] E n).det := by
  change LinearMap.det (ρ • (L : E n →ₗ[ℝ] E n)) = _
  rw [LinearMap.det_smul]
  simp [E,Reference.Space]

/-- Unit-determinant Hessian normalization preserves the literal density:
the new density is exactly the old density evaluated at the physical point. -/
theorem alexandrov_density_improvementRescale {u f : E n → ℝ}
    (L : E n ≃L[ℝ] E n) (hL : (L : E n →L[ℝ] E n).det=1) (p : E n)
    {ρ : ℝ} (hρ : 0 < ρ) {A : Set (E n)} (hA : IsCompact A)
    (hMA : volume (subgradientImage u ((fun x => ρ • L x) '' A)) =
      ∫⁻ y in (fun x => ρ • L x) '' A, ENNReal.ofReal (f y)) :
    volume (subgradientImage (improvementRescale u p L ρ) A) =
      ∫⁻ y in A, ENNReal.ofReal (f (ρ • L y)) := by
  let M := improvementCoordinateMap L hρ.ne'
  have he : affineSource M.symm 0 = fun x => ρ • L x := by
    funext x
    simp [affineSource,M]
  have hMdet : (M : E n →L[ℝ] E n).det=ρ^n := by
    rw [improvementCoordinateMap_det,hL,mul_one]
  have hh := alexandrov_density_affine_vertical M.symm 0 p (u 0)
    (t:=(ρ^2)⁻¹) (by positivity) hA (by simpa only [he] using hMA)
  have hpotential : (fun y => (ρ^2)⁻¹*affinePotential u M.symm 0 p (u 0) y) =
      improvementRescale u p L ρ := by
    funext y
    simp only [affinePotential,he,improvementRescale]
    change (ρ^2)⁻¹*(u (ρ • L y)-inner ℝ p (ρ • L y)-u 0) =
      (u (ρ • L y)-u 0-inner ℝ p (ρ • L y))/ρ^2
    ring
  rw [hpotential] at hh
  convert hh using 1
  apply lintegral_congr
  intro y
  simp only [ContinuousLinearEquiv.symm_symm,hMdet,abs_of_nonneg (pow_nonneg hρ.le _),he]
  congr 1
  have hcancel : ((ρ^2)⁻¹)^n*(ρ^n)^2=1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hρ.ne'),one_pow]
  rw [hcancel,one_mul]

end GaussianTilt.MomentMapRegularity
