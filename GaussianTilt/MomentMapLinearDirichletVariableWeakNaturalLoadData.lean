import GaussianTilt.MomentMapLinearDirichletNaturalData
import GaussianTilt.MomentMapLinearDirichletCoordinateJetFieldsHolder
import GaussianTilt.MomentMapLinearDirichletVariableWeakClosedGeometry

/-! # Actual natural scalar/vector load data for both weak boundary passes -/
noncomputable section
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- A real raw Hölder vector-load representative supplies the exact
Euclidean natural load record, with its AE identification retained. -/
theorem exists_natural_vector_load_bounds_of_raw_holder
    (j : Fin n) (R : ℝ) {β : ℝ} (hβ : 0≤β)
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (g : CoordinateSpace n → CoordinateSpace n)
    (hg : BoundedHolderOn β g (coordinateClosedHalfBall j R))
    (hG : ∀ i,∀ᵐ x∂volume,x∈coordinateHalfBall j R → G i x=g x i) :
    ∃ H : ℝ,0≤H ∧ WeakHalfBallLoadBounds j R β 0 H
      (0 : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) G (g ∘ dirichletCoordinateEquiv n) := by
  obtain ⟨H,hH,_,hh⟩ := boundedHolderOn_comp_coordinateEquiv hβ hg
  refine ⟨H,hH,⟨le_rfl,hH,?_,?_,?_⟩⟩
  · filter_upwards [Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=(volume : Measure (CoordinateSpace n)))] with x hx _
    simpa only [hx,Pi.zero_apply,abs_zero] using (le_rfl : (0:ℝ)≤0)
  · intro i
    filter_upwards [hG i] with x hx hxU
    simpa only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply] using hx hxU
  · intro x hx hxj y hy hyj i
    have hxS : x∈(dirichletCoordinateEquiv n) ⁻¹' coordinateClosedHalfBall j R := by
      refine ⟨?_,hxj⟩
      simpa only [rawChartClosedBall,mem_setOf_eq,ContinuousLinearEquiv.symm_apply_apply] using hx
    have hyS : y∈(dirichletCoordinateEquiv n) ⁻¹' coordinateClosedHalfBall j R := by
      refine ⟨?_,hyj⟩
      simpa only [rawChartClosedBall,mem_setOf_eq,ContinuousLinearEquiv.symm_apply_apply] using hy
    exact (norm_le_pi_norm ((g ∘ dirichletCoordinateEquiv n) x-(g ∘ dirichletCoordinateEquiv n) y) i).trans
      (hh x hxS y hyS)

/-- A bounded actual scalar representative gives a natural scalar-only
load; the vector load is the genuine zero L² class and zero function. -/
theorem natural_scalar_load_bounds_of_raw_bound
    (j : Fin n) (R β : ℝ) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (f₀ : CoordinateSpace n→ℝ) {F : ℝ} (hF : 0≤F)
    (hfb : ∀ x∈coordinateClosedHalfBall j R,|f₀ x|≤F)
    (hf : ∀ᵐ x∂volume,x∈coordinateHalfBall j R → f x=f₀ x) :
    WeakHalfBallLoadBounds j R β F 0 f (fun _=>0) (fun _ _=>0) := by
  refine ⟨hF,le_rfl,?_,?_,?_⟩
  · filter_upwards [hf] with x hx hxU
    rw [hx hxU]
    exact hfb x (coordinateHalfBall_subset_closed j R hxU)
  · intro i
    filter_upwards [Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=(volume : Measure (CoordinateSpace n)))] with x hx _
    exact hx
  · intro x hx hxj y hy hyj i
    simp only [sub_self,abs_zero,zero_mul,le_refl]

/-- The scalar bound is also constructed from literal bounded Hölder data. -/
theorem exists_natural_scalar_load_bounds_of_raw_holder
    (j : Fin n) (R β : ℝ) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (f₀ : CoordinateSpace n→ℝ)
    (hholder : BoundedHolderOn β f₀ (coordinateClosedHalfBall j R))
    (hf : ∀ᵐ x∂volume,x∈coordinateHalfBall j R → f x=f₀ x) :
    ∃ F : ℝ,0≤F ∧ WeakHalfBallLoadBounds j R β F 0 f (fun _=>0) (fun _ _=>0) := by
  obtain ⟨F,hF,hb,_⟩ := hholder
  exact ⟨F,hF,natural_scalar_load_bounds_of_raw_bound j R β f f₀ hF hb hf⟩

end GaussianTilt.MomentMapLinearDirichlet
