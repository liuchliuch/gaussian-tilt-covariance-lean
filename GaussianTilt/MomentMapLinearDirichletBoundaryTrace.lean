import GaussianTilt.MomentMapLinearDirichletBoundaryBarrier

/-!
# An actual boundary-continuous representative of the weak inverse

The proved defining-function bound permits a concrete null-set correction
of the L² representative. The corrected function has the same L² class,
vanishes outside the domain, and is genuinely continuous at every zero of
the defining function, in particular every boundary point. Interior
regularity is separate and is not assumed here.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Null-set correction turns an actual almost-everywhere continuous
barrier into genuine continuity at its zero set. -/
theorem exists_boundary_continuous_representative
    {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω)
    (u : dirichletSobolev Ω) {w : CoordinateSpace n → ℝ} (hw : Continuous w)
    {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂volume, x ∈ Ω → |dirichletValue Ω u x| ≤ B * |w x|) :
    ∃ v : CoordinateSpace n → ℝ,
      v =ᵐ[volume] dirichletValue Ω u ∧
      (∀ x ∉ Ω, v x = 0) ∧
      (∀ x, |v x| ≤ B * |w x|) ∧
      (∀ x, w x = 0 → v x = 0 ∧ ContinuousAt v x) := by
  classical
  let v := fun x => if x ∈ Ω ∧ |dirichletValue Ω u x| ≤ B * |w x| then dirichletValue Ω u x else 0
  have hv (x : CoordinateSpace n) : |v x| ≤ B * |w x| := by
    by_cases hx : x ∈ Ω ∧ |dirichletValue Ω u x| ≤ B * |w x|
    · simpa only [v, if_pos hx] using hx.2
    · simp only [v, if_neg hx, abs_zero]
      exact mul_nonneg hB (abs_nonneg _)
  refine ⟨v, ?_, ?_, hv, ?_⟩
  · filter_upwards [hu, dirichletValue_ae_zero_outside hΩ u] with x hx hz
    by_cases hxΩ : x ∈ Ω
    · exact if_pos ⟨hxΩ, hx hxΩ⟩
    · simp only [v, hxΩ, false_and, ↓reduceIte]
      exact (hz hxΩ).symm
  · intro x hx
    simp [v, hx]
  · intro x hx
    have hvx : v x = 0 := by
      have hb := hv x
      rw [hx, abs_zero, mul_zero] at hb
      exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    refine ⟨hvx, ?_⟩
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [hvx, sub_zero, Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun y => abs_nonneg (v y)))
      (Eventually.of_forall hv)
    simpa only [hx, abs_zero, mul_zero] using
      (tendsto_const_nhds.mul hw.continuousAt.tendsto.abs :
        Tendsto (fun y => B * |w y|) (𝓝 x) (𝓝 (B * |w x|)))

/-- The genuinely constructed weak inverse admits a representative that
is zero and continuous at every boundary point of a smooth defining domain. -/
theorem weakDirichletLaplaceSolution_boundary_continuous_representative
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (hw0 : ∀ x ∈ Ω, w x ≤ 0)
    (hwb : ∀ x ∈ frontier Ω, w x = 0)
    {a F : ℝ} (ha : 0 < a) (hF : 0 ≤ F)
    (hwlap : ∀ x ∈ Ω, a ≤ euclideanLaplacian w x)
    (hf : ∀ᵐ x ∂volume, x ∈ Ω → |f x| ≤ F) :
    ∃ v : CoordinateSpace n → ℝ,
      v =ᵐ[volume] dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f) ∧
      (∀ x ∉ Ω, v x = 0) ∧
      (∀ x, |v x| ≤ (F / a) * |w x|) ∧
      (∀ x ∈ frontier Ω, v x = 0 ∧ ContinuousAt v x) := by
  have hbar := weakDirichletLaplaceSolution_defining_barrier hΩ hΩb i hR hstrip f hw hw0 ha hF hwlap hf
  obtain ⟨v, hv, hvout, hvbound, hvcont⟩ := exists_boundary_continuous_representative hΩ.measurableSet
    (weakDirichletLaplaceSolution i hR hstrip f) hw.continuous (div_nonneg hF ha.le) (by
      filter_upwards [hbar] with x hx hxΩ
      rw [abs_of_nonpos (hw0 x hxΩ)]
      convert hx hxΩ using 1 <;> ring)
  exact ⟨v, hv, hvout, hvbound, fun x hx => hvcont x (hwb x hx)⟩

end GaussianTilt.MomentMapLinearDirichlet
