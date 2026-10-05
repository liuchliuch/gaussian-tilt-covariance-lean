import GaussianTilt.MomentMapLinearDirichletWeakGradientClassicalCoordinates
import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceGeometry

/-! # Actual tangential derivatives vanish on the flat zero boundary

A genuine within-derivative is restricted to an actual short line in the
boundary plane. No smooth extension of the weak solution is used.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- A true within-derivative annihilates every tangent vector at an
interior point of the flat face where the function is genuinely zero. -/
theorem within_derivative_tangent_zero_on_flat_face
    (q : Fin n) {R : ℝ} {u : CoordinateSpace n→ℝ} {z v : CoordinateSpace n}
    {D : CoordinateSpace n→L[ℝ]ℝ}
    (hz : ‖(coordinateEquiv n).symm z‖<R) (hzq : z q=0) (hvq : v q=0)
    (hD : HasFDerivWithinAt u D {x : CoordinateSpace n | ‖(coordinateEquiv n).symm x‖≤R ∧ 0≤x q} z)
    (hzero : ∀ x : CoordinateSpace n,‖(coordinateEquiv n).symm x‖≤R → x q=0 → u x=0) :
    D v=0 := by
  let γ : ℝ → CoordinateSpace n := fun t=>z+t • v
  have hγ : HasDerivAt γ v 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z
  have hγ0 : γ 0=z := by simp only [γ,zero_smul,add_zero]
  have hn : Tendsto (fun t=>‖(coordinateEquiv n).symm (γ t)‖) (𝓝 (0:ℝ))
      (𝓝 ‖(coordinateEquiv n).symm z‖) := by
    simpa only [Function.comp_apply,hγ0] using ((coordinateEquiv n).symm.continuous.continuousAt.comp hγ.continuousAt).norm.tendsto
  have hq (t : ℝ) : (γ t) q=0 := by simp only [γ,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hzq,hvq,mul_zero,add_zero]
  have hmaps : ∀ᶠ t in 𝓝 (0:ℝ),γ t∈{x : CoordinateSpace n | ‖(coordinateEquiv n).symm x‖≤R ∧ 0≤x q} := by
    filter_upwards [(tendsto_order.mp hn).2 R hz] with t ht
    exact ⟨ht.le,by rw [hq]⟩
  have hD' : HasFDerivWithinAt u D {x : CoordinateSpace n | ‖(coordinateEquiv n).symm x‖≤R ∧ 0≤x q} (γ 0) := by
    rw [hγ0]
    exact hD
  have hcomp := hD'.comp_hasDerivAt 0 hγ hmaps
  have he : u ∘ γ=ᶠ[𝓝 (0:ℝ)] (fun _=>0) := by
    filter_upwards [hmaps] with t ht
    exact hzero (γ t) ht.1 (hq t)
  have hzder : HasDerivAt (u ∘ γ) 0 0 := (hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq he
  exact hcomp.unique hzder

/-- In particular, the actual continuous first-gradient representative
has zero tangential components on the flat face. -/
theorem coordinate_gradient_tangent_zero_on_flat_face
    (q i : Fin n) (hi : i≠q) {R : ℝ} {u : CoordinateSpace n→ℝ}
    {G : CoordinateSpace n → CoordinateSpace n} {z : CoordinateSpace n}
    (hz : ‖(coordinateEquiv n).symm z‖<R) (hzq : z q=0)
    (hD : HasFDerivWithinAt u (coordinateCovector (G z))
      {x : CoordinateSpace n | ‖(coordinateEquiv n).symm x‖≤R ∧ 0≤x q} z)
    (hzero : ∀ x : CoordinateSpace n,‖(coordinateEquiv n).symm x‖≤R → x q=0 → u x=0) :
    G z i=0 := by
  simpa only [coordinateCovector_single] using within_derivative_tangent_zero_on_flat_face q hz hzq
    (show (Pi.single i 1 : CoordinateSpace n) q=0 by simp [Ne.symm hi]) hD hzero

end GaussianTilt.MomentMapLinearDirichlet
