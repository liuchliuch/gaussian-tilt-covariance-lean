import GaussianTilt.MomentMapLinearDirichletVariableWeakExtension

/-! # Literal scalar forcing bounds under the genuine weak chart pullback -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1200000

lemma ae_comp_on_patch {S : Set (CoordinateSpace n)} (hS : MeasurableSet S)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : Measurable ψ)
    {C : ℝ} (hmap : (volume.restrict S).map ψ ≤ ENNReal.ofReal (C^2) • volume)
    {P : CoordinateSpace n → Prop} (hP : ∀ᵐ x∂volume, P x) :
    ∀ᵐ x∂volume, x∈S → P (ψ x) := by
  have hq : Measure.QuasiMeasurePreserving ψ (volume.restrict S) volume :=
    ⟨hψ,Measure.absolutelyContinuous_of_le_smul hmap⟩
  exact (ae_restrict_iff' hS).mp (hq.tendsto_ae.eventually hP)

/-- A bounded physical scalar load remains genuinely bounded after chart
pullback; the new bound is the actual compact Jacobian maximum. -/
theorem masked_jacobian_load_bounded {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ)
    {C : ℝ} (hmap : (volume.restrict S).map ψ ≤ ENNReal.ofReal (C^2) • volume)
    {f g : CoordinateSpace n → ℝ}
    (hg : g =ᵐ[volume] S.indicator (fun x=>|(fderiv ℝ ψ x).det| * f (ψ x)))
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ᵐ x∂volume, |f x| ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x∂volume, |g x| ≤ B := by
  obtain ⟨J,hJ⟩ := hS.exists_bound_of_continuousOn (contDiff_chartJacobian_det hψ).continuous.abs.continuousOn
  refine ⟨max J 0*M,mul_nonneg (le_max_right _ _) hM,?_⟩
  have hfψ := ae_comp_on_patch hS.measurableSet hψ.continuous.measurable hmap hf
  filter_upwards [hg,hfψ] with x hx hfx
  rw [hx]
  by_cases hxS : x∈S
  · rw [indicator_of_mem hxS,abs_mul,abs_abs]
    apply mul_le_mul _ (hfx hxS) (abs_nonneg _) (le_max_right J 0)
    simpa only [Real.norm_eq_abs,abs_abs] using (hJ x hxS).trans (le_max_left J 0)
  · rw [indicator_of_notMem hxS,abs_zero]
    exact mul_nonneg (le_max_right _ _) hM

/-- Changes of the original L² representative remain null changes of the
actual transformed load, by the derived measure-distortion bound. -/
lemma jacobian_load_eq_ae_of_physical_eq_ae {S : Set (CoordinateSpace n)} (hS : MeasurableSet S)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : Measurable ψ)
    {C : ℝ} (hmap : (volume.restrict S).map ψ ≤ ENNReal.ofReal (C^2) • volume)
    {f f' : CoordinateSpace n → ℝ} (hf : f =ᵐ[volume] f') :
    S.indicator (fun x=>|(fderiv ℝ ψ x).det| *f (ψ x)) =ᵐ[volume]
      S.indicator (fun x=>|(fderiv ℝ ψ x).det| *f' (ψ x)) := by
  filter_upwards [ae_comp_on_patch hS hψ hmap hf] with x hx
  by_cases hxS : x∈S
  · simp only [indicator_of_mem hxS,hx hxS]
  · simp only [indicator_of_notMem hxS]

end GaussianTilt.MomentMapLinearDirichlet
