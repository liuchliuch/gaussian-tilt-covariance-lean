import GaussianTilt.MomentMapLinearDirichletVariableWeakComposition
import GaussianTilt.MomentMapLinearDirichletQuantitativeChartRaw

/-! # Actual chart measure distortion from the inverse Jacobian

The L² chart pullback is controlled by the genuine area formula. The
measure inequality is proved, rather than assumed for the chart map.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma map_restrict_le_of_jacobian_lower {V : Set (CoordinateSpace n)} (hV : MeasurableSet V)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : Measurable ψ)
    {D : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
    (hD : ∀ x∈V, HasFDerivAt ψ (D x) x) (hinj : InjOn ψ V)
    {lam : ℝ} (hlam : 0 < lam) (hdet : ∀ x∈V, lam≤|(D x).det|) :
    (volume.restrict V).map ψ≤(ENNReal.ofReal lam)⁻¹ • volume := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hψ hA,Measure.restrict_apply (hψ hA),Measure.smul_apply,smul_eq_mul]
  let S := ψ ⁻¹' A∩V
  have hS : MeasurableSet S := (hψ hA).inter hV
  have hl : ENNReal.ofReal lam*volume S≤volume A := by
    calc
      _ = ∫⁻ x in S, ENNReal.ofReal lam := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in S, ENNReal.ofReal |(D x).det| := by
        apply setLIntegral_mono' hS
        intro x hx
        exact ENNReal.ofReal_le_ofReal (hdet x hx.2)
      _ = volume (ψ '' S) := lintegral_abs_det_fderiv_eq_addHaar_image volume hS
        (fun x hx=>(hD x hx.2).hasFDerivWithinAt) (hinj.mono inter_subset_right)
      _ ≤ volume A := measure_mono (by rintro _ ⟨x,hx,rfl⟩; exact hx.1)
  have hmul := mul_le_mul_left' hl (ENNReal.ofReal lam)⁻¹
  have hc0 : ENNReal.ofReal lam≠0 := (ENNReal.ofReal_pos.mpr hlam).ne'
  simpa only [← mul_assoc,ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top,one_mul,S] using hmul

/-- Compact local inverse charts have a genuine positive Jacobian minimum
when their actual derivative is invertible. -/
lemma exists_jacobian_lower_on_compact {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {ψ : CoordinateSpace n → CoordinateSpace n}
    (hD : ContinuousOn (fderiv ℝ ψ) S) (hdet : ∀ x∈S, (fderiv ℝ ψ x).det≠0) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x∈S, lam≤|(fderiv ℝ ψ x).det| := by
  have hc : ContinuousOn (fun x=>|(fderiv ℝ ψ x).det|) S :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn hD).abs
  by_cases hSn : S.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hS.exists_isMinOn hSn hc
    exact ⟨|(fderiv ℝ ψ x).det|,abs_pos.mpr (hdet x hx),fun y hy=>hmin hy⟩
  · exact ⟨1,by norm_num,fun x hx=>False.elim (hSn ⟨x,hx⟩)⟩

end GaussianTilt.MomentMapLinearDirichlet
