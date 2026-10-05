import GaussianTilt.MomentMapLinearDirichletVariableEnergyBounds

/-! # Actual scalar and divergence loads with scale-correct energy bounds -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The literal scalar-plus-divergence weak load. A minus sign in a chosen
PDE convention is implemented by replacing G with -G. -/
def variableScalarVectorLoad (Ω : Set (CoordinateSpace n))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    dirichletSobolev Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (dirichletValue Ω) +
    ∑ i, (innerSL ℝ (G i)).comp ((volumeJetDerivative i).comp (dirichletSobolev Ω).subtypeL)

lemma variableScalarVectorLoad_apply (Ω : Set (CoordinateSpace n))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (v : dirichletSobolev Ω) :
    variableScalarVectorLoad Ω f G v = inner ℝ f (dirichletValue Ω v) +
      ∑ i, inner ℝ (G i) (v.1 i.succ) := by
  simp only [variableScalarVectorLoad, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, innerSL_apply]
  rfl

/-- The actual bounded-domain Poincaré inequality supplies the radius
factor for scalar forcing, while the vector load couples directly to gradient energy. -/
theorem variableScalarVectorLoad_abs_le_gradient {Ω : Set (CoordinateSpace n)}
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (v : dirichletSobolev Ω) :
    |variableScalarVectorLoad Ω f G v| ≤ (2*R*‖f‖ + ∑ k, ‖G k‖) * jetGradientNorm v.1 := by
  have hv : ‖dirichletValue Ω v‖ ≤ 2*R*jetGradientNorm v.1 :=
    (dirichlet_poincare_strip i hR hΩ v).trans
      (mul_le_mul_of_nonneg_left (norm_jetDerivative_le_gradient v.1 i) (by positivity))
  have hscalar : |inner ℝ f (dirichletValue Ω v)| ≤ (2*R*‖f‖)*jetGradientNorm v.1 := by
    have hh := (abs_real_inner_le_norm f (dirichletValue Ω v)).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg f))
    nlinarith
  have hvector : |∑ k, inner ℝ (G k) (v.1 k.succ)| ≤ (∑ k, ‖G k‖)*jetGradientNorm v.1 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => (abs_real_inner_le_norm (G k) _).trans
      (mul_le_mul_of_nonneg_left (norm_jetDerivative_le_gradient v.1 k) (norm_nonneg _)))
  rw [variableScalarVectorLoad_apply]
  exact (abs_add_le _ _).trans ((add_le_add hscalar hvector).trans_eq (by ring))

end GaussianTilt.MomentMapLinearDirichlet
