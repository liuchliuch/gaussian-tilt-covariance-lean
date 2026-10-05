import GaussianTilt.MomentMapLinearDirichletVariableWeakFlattening

/-! # Exact divergence-form energy under a genuine nonlinear chart

The original vector field may be only a weak L² gradient. No derivative of
that vector field occurs in the formula; only the chart and the compact
test are differentiated.
-/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1200000

def chartJacobian (ψ : CoordinateSpace n → CoordinateSpace n) (x : CoordinateSpace n) :
    Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix' (fderiv ℝ ψ x).toLinearMap

@[simp] lemma chartJacobian_entry (ψ : CoordinateSpace n → CoordinateSpace n) (x : CoordinateSpace n) (i j : Fin n) :
    chartJacobian ψ x i j=chartDerivativeEntry ψ j i x := rfl

lemma coordinateGradient_comp_chart {F : CoordinateSpace n → CoordinateSpace n}
    {τ : CoordinateSpace n → ℝ} (hF : Differentiable ℝ F) (hτ : Differentiable ℝ τ) (x : CoordinateSpace n) :
    coordinateGradient (τ ∘ F) x=(chartJacobian F x)ᵀ *ᵥ coordinateGradient τ (F x) := by
  ext i
  change coordinateDerivative i (τ ∘ F) x=_
  rw [coordinateDerivative_comp_chart hF hτ]
  rfl

lemma chartJacobian_inverse_of_left_inverse {V : Set (CoordinateSpace n)} (hV : IsOpen V)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF : Differentiable ℝ F)
    (hψ : DifferentiableOn ℝ ψ V) (hleft : ∀ x∈V, F (ψ x)=x) {x : CoordinateSpace n} (hx : x∈V) :
    chartJacobian ψ x*chartJacobian F (ψ x)=1 := by
  have he : F ∘ ψ=ᶠ[𝓝 x] id := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hleft y hy
  have hd := (he.fderiv (𝕜:=ℝ)).self_of_nhds
  rw [fderiv_comp x (hF _) ((hψ x hx).differentiableAt (hV.mem_nhds hx)),fderiv_id] at hd
  have hm := congrArg (fun T : CoordinateSpace n →L[ℝ] CoordinateSpace n=>LinearMap.toMatrix' T.toLinearMap) hd
  change LinearMap.toMatrix' ((fderiv ℝ F (ψ x)).toLinearMap.comp (fderiv ℝ ψ x).toLinearMap)=
    LinearMap.toMatrix' (LinearMap.id : CoordinateSpace n →ₗ[ℝ] CoordinateSpace n) at hm
  rw [LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id] at hm
  exact Matrix.mul_eq_one_comm.mp hm

lemma chart_energy_algebra {G J : Matrix (Fin n) (Fin n) ℝ} (hGJ : G*J=1)
    (u q : CoordinateSpace n) (d : ℝ) :
    (Gᵀ *ᵥ u) ⬝ᵥ ((d • (J*Jᵀ)) *ᵥ q)=d*(u ⬝ᵥ (Jᵀ *ᵥ q)) := by
  rw [Matrix.smul_mulVec,dotProduct_smul]
  change d*((Gᵀ *ᵥ u) ⬝ᵥ ((J*Jᵀ) *ᵥ q))=_
  congr 1
  calc
    _ = ((J*Jᵀ) *ᵥ q) ⬝ᵥ (Gᵀ *ᵥ u) := dotProduct_comm _ _
    _ = (((J*Jᵀ) *ᵥ q) ᵥ* Gᵀ) ⬝ᵥ u := Matrix.dotProduct_mulVec _ _ _
    _ = (G *ᵥ ((J*Jᵀ) *ᵥ q)) ⬝ᵥ u := by rw [Matrix.vecMul_transpose]
    _ = (Jᵀ *ᵥ q) ⬝ᵥ u := by rw [Matrix.mulVec_mulVec,← Matrix.mul_assoc,hGJ,one_mul]
    _ = _ := dotProduct_comm _ _

/-- The actual divergence coefficient is the Jacobian-weighted Gram
matrix of the forward derivative. -/
def divergenceChartCoefficient (F ψ : CoordinateSpace n → CoordinateSpace n) (z : CoordinateSpace n) :
    Matrix (Fin n) (Fin n) ℝ :=
  |(fderiv ℝ ψ z).det| • (chartJacobian F (ψ z)*(chartJacobian F (ψ z))ᵀ)

def weakChartGradient (ψ : CoordinateSpace n → CoordinateSpace n)
    (G : CoordinateSpace n → CoordinateSpace n) (z : CoordinateSpace n) : CoordinateSpace n :=
  (chartJacobian ψ z)ᵀ *ᵥ G (ψ z)

/-- Exact energy change of variables for an arbitrary original vector
field and a genuine smooth compact-test gradient. It uses the actual
inverse identity and the area formula, with no weak-solution regularity
premise. -/
theorem chart_energy_change_of_variables {V : Set (CoordinateSpace n)} (hV : IsOpen V)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF : Differentiable ℝ F)
    (hψ : DifferentiableOn ℝ ψ V) (hleft : ∀ x∈V, F (ψ x)=x)
    (G : CoordinateSpace n → CoordinateSpace n) {τ : CoordinateSpace n → ℝ} (hτ : Differentiable ℝ τ) :
    (∫ z in V, weakChartGradient ψ G z ⬝ᵥ (divergenceChartCoefficient F ψ z *ᵥ coordinateGradient τ z))=
      ∫ x in ψ '' V, G x ⬝ᵥ coordinateGradient (τ ∘ F) x := by
  have hinj : InjOn ψ V := by
    intro x hx y hy hxy
    rw [← hleft x hx,← hleft y hy,hxy]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hV.measurableSet
    (fun x hx=>((hψ x hx).differentiableAt (hV.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt) hinj]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
  rw [coordinateGradient_comp_chart hF hτ,hleft z hz]
  exact chart_energy_algebra (chartJacobian_inverse_of_left_inverse hV hF hψ hleft hz) (G (ψ z)) (coordinateGradient τ z) |(fderiv ℝ ψ z).det|

lemma chart_forcing_change_of_variables {V : Set (CoordinateSpace n)} (hV : IsOpen V)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hψ : DifferentiableOn ℝ ψ V)
    (hleft : ∀ x∈V, F (ψ x)=x) (f τ : CoordinateSpace n → ℝ) :
    (∫ x in ψ '' V, f x*τ (F x))=∫ z in V, |(fderiv ℝ ψ z).det| *f (ψ z)*τ z := by
  have hinj : InjOn ψ V := by
    intro x hx y hy hxy
    rw [← hleft x hx,← hleft y hy,hxy]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hV.measurableSet
    (fun x hx=>((hψ x hx).differentiableAt (hV.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt) hinj]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
  rw [hleft z hz]
  change |(fderiv ℝ ψ z).det| *(f (ψ z)*τ z)=_
  ring

end GaussianTilt.MomentMapLinearDirichlet
