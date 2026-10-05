import GaussianTilt.MomentMapLinearDirichletRestrictedEnergy
import GaussianTilt.MomentMapLinearDirichletVariableLoads

/-! # Genuine local scalar/vector forcing norms for the replacement estimate -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma inner_L2_mask_left_of_zero_exterior (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (f g : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hg : ∀ᵐ x ∂volume, x ∉ Ω → g x=0) :
    inner ℝ f g = inner ℝ (maskL2 Ω hΩ f) g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg, maskL2_ae Ω hΩ f] with x hx hm
  by_cases hxΩ : x ∈ Ω
  · rw [hm, indicator_of_mem hxΩ]
  · rw [hx hxΩ]
    simp

/-- Restricting the data to Ω leaves the actual H₀¹ load unchanged. -/
theorem variableScalarVectorLoad_mask (Ω : Set (CoordinateSpace n)) (hΩ : MeasurableSet Ω)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    variableScalarVectorLoad Ω f G =
      variableScalarVectorLoad Ω (maskL2 Ω hΩ f) (fun i => maskL2 Ω hΩ (G i)) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [variableScalarVectorLoad_apply, variableScalarVectorLoad_apply,
    inner_L2_mask_left_of_zero_exterior Ω hΩ f (dirichletValue Ω v) (dirichletValue_ae_zero_outside hΩ v)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact inner_L2_mask_left_of_zero_exterior Ω hΩ (G i) (v.1 i.succ) (dirichletGradient_ae_zero_outside hΩ v i)

/-- Both forcing norms are genuinely local. In particular, the scalar
forcing has the correct local radius factor in the energy recurrence. -/
theorem variableScalarVectorLoad_abs_le_local_gradient {Ω : Set (CoordinateSpace n)}
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R) (hΩ : MeasurableSet Ω)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (v : dirichletSobolev Ω) :
    |variableScalarVectorLoad Ω f G v| ≤
      (2*R*‖maskL2 Ω hΩ f‖ + ∑ k, ‖maskL2 Ω hΩ (G k)‖) * jetGradientNorm v.1 := by
  rw [variableScalarVectorLoad_mask Ω hΩ f G]
  exact variableScalarVectorLoad_abs_le_gradient i hR hstrip _ _ v

end GaussianTilt.MomentMapLinearDirichlet
