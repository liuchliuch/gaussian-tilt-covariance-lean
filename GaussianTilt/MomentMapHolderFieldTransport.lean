import GaussianTilt.MomentMapHolderChartBounds

/-! # Actual fixed Lipschitz-chart transport of every Hölder datum -/
noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem exists_holder_field_pullback {S : Set F} {T : Set E} (hTc : IsCompact T)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) (ψ : E → F)
    (hψ : ContinuousOn ψ T) (hmap : MapsTo ψ T S)
    (hLip : ∀ x ∈ T, ∀ y ∈ T, ‖ψ x-ψ y‖ ≤ K*‖x-y‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Space S V α, ∃ g : Space T V α,
      ‖g‖ ≤ C*‖f‖ ∧ ∀ x : T, value T V α g x = extendValue α f (ψ x) := by
  letI : CompactSpace T := isCompact_iff_compactSpace.mp hTc
  let C := max 1 (K^α)
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro f
  obtain ⟨hb,hh⟩ := holder_field_comp_bounds hα hK (norm_nonneg f) ψ hmap hLip f le_rfl
  let b : T →ᵇ V := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => extendValue α f (ψ x),
      continuousOn_iff_continuous_restrict.mp ((continuousOn_extendValue α f).comp hψ hmap)⟩
  have hbc : ∀ x y : T, ‖b x-b y‖ ≤ (C*‖f‖)*dist x y^α := by
    intro x y
    have he : ‖f‖*K^α ≤ C*‖f‖ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right (le_max_right 1 (K^α)) (norm_nonneg f)
    exact (hh x x.2 y y.2).trans (by
      simpa only [Subtype.dist_eq,dist_eq_norm] using mul_le_mul_of_nonneg_right he
        (Real.rpow_nonneg (norm_nonneg ((x:E)-y)) α))
  let g := ofBounded T V α b (C*‖f‖) hbc
  refine ⟨g,?_,fun _ => rfl⟩
  apply (norm_ofBounded_le T V α b (mul_nonneg hC (norm_nonneg f)) hbc).trans
  apply max_le _ le_rfl
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg f))).mpr
  intro x
  exact (hb x x.2).trans (by nlinarith [mul_le_mul_of_nonneg_right (le_max_left 1 (K^α)) (norm_nonneg f)])

/-- In particular every raw Hölder datum transports through an actual
continuous linear coordinate equivalence, with its genuine operator norm. -/
theorem exists_holder_field_linearEquiv_pullback {S : Set F} {T : Set E}
    (hTc : IsCompact T) {α : ℝ} (hα : 0 ≤ α) (e : E ≃L[ℝ] F)
    (hmap : MapsTo e T S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Space S V α, ∃ g : Space T V α,
      ‖g‖ ≤ C*‖f‖ ∧ ∀ x : T, value T V α g x = extendValue α f (e x) := by
  apply exists_holder_field_pullback hTc hα (norm_nonneg e.toContinuousLinearMap) e e.continuous.continuousOn hmap
  intro x hx y hy
  rw [← map_sub]
  exact e.toContinuousLinearMap.le_opNorm (x-y)

end GaussianTilt.HolderSpace
