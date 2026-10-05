import GaussianTilt.MomentMapRegularityImprovementSeedScales
import GaussianTilt.MomentMapRegularityImprovementComposition

/-! # The actual reference seed in the physical coordinates of the recurrence -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma improvementRescale_repeated_identity (u : E n → ℝ) (p : E n)
    (L : E n ≃L[ℝ] E n) {ρ R : ℝ} (hρ : ρ≠0) (hR : R≠0) :
    improvementRescale (improvementRescale u p L (ρ/R)) 0 (ContinuousLinearMap.id ℝ (E n)) R=
      improvementRescale u p L ρ := by
  funext y
  simp only [improvementRescale,map_zero,smul_zero,inner_zero_left,inner_zero_right,
    sub_zero,ContinuousLinearMap.id_apply,map_smul,real_inner_smul_right,smul_smul]
  have he : (ρ/R)*R=ρ := div_mul_cancel₀ _ hR
  rw [he]
  field_simp
  ring

/-- Two genuine rescalings put the initial source into the exact seed
format of the adaptive recurrence and make its local density Hölder
constant at most one. The Alexandrov law is transferred literally. -/
theorem normalized_seed_recurrence_data {u g : E n → ℝ}
    (huc : Continuous u) (hc : ConvexOn ℝ univ u) (hgc : Continuous g)
    (hMA : ∀ A, IsCompact A → volume (subgradientImage u A)=
      (volume.withDensity (fun y=>ENNReal.ofReal (g y))) A)
    (L : E n ≃L[ℝ] E n) (p : E n) (hdet : (L : E n →L[ℝ] E n).det=1)
    {ρ R r N F α η : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hN : 0≤N) (hF : 0≤F) (hα : 0≤α)
    (hL : ‖(L : E n →L[ℝ] E n)‖≤N) (hregion : 2*ρ*N≤r)
    (hsmall : F*(ρ*N/R)^α≤1)
    (hg : ∀ y, ‖y‖≤r → |g y-1|≤F*‖y‖^α)
    (hseed : ∀ y, ‖y‖≤1 → |improvementRescale u p L ρ y-‖y‖^2/2|≤η) :
    let U := improvementRescale u p L (ρ/R)
    let f := fun y:E n=>g ((ρ/R) • L y)
    Continuous U ∧ ConvexOn ℝ univ U ∧ Continuous f ∧
      (∀ A, IsCompact A → volume (subgradientImage U A)=
        (volume.withDensity (fun y=>ENNReal.ofReal (f y))) A) ∧
      (∀ y, ‖y‖≤2*R → |f y-1|≤‖y‖^α) ∧
      ∀ y, ‖y‖≤1 → |improvementRescale U 0 (ContinuousLinearMap.id ℝ (E n)) R y-‖y‖^2/2|≤η := by
  dsimp only
  have ht : 0 < ρ/R := div_pos hρ hR
  refine ⟨improvementRescale_continuous huc p L _,improvementRescale_convex hc p L _,by fun_prop,?_,?_,?_⟩
  · intro A hA
    rw [withDensity_apply _ hA.measurableSet]
    apply alexandrov_density_improvementRescale L hdet p ht hA
    have hi : IsCompact ((fun y:E n=>(ρ/R) • L y) '' A) := hA.image (by fun_prop)
    rw [hMA _ hi,withDensity_apply _ hi.measurableSet]
  · intro y hy
    have hnorm : ‖(ρ/R) • L y‖≤(ρ*N/R)*‖y‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      have hh := ((L : E n →L[ℝ] E n).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
      have hh' := mul_le_mul_of_nonneg_left hh ht.le
      convert hh' using 1 <;> ring
    have hmem : ‖(ρ/R) • L y‖≤r := by
      have hh := mul_le_mul_of_nonneg_left hy (by positivity : 0≤ρ*N/R)
      have he : (ρ*N/R)*(2*R)=2*ρ*N := by field_simp
      rw [he] at hh
      exact hnorm.trans (hh.trans hregion)
    have hh := (hg _ hmem).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm hα) hF)
    rw [Real.mul_rpow (by positivity : 0≤ρ*N/R) (norm_nonneg _)] at hh
    have hlast := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (norm_nonneg y) α)
    calc
      _ ≤ (F*(ρ*N/R)^α)*‖y‖^α := by simpa only [mul_assoc] using hh
      _ ≤ _ := by simpa only [one_mul] using hlast
  · rw [improvementRescale_repeated_identity u p L hρ.ne' hR.ne']
    exact hseed

end GaussianTilt.MomentMapRegularity
