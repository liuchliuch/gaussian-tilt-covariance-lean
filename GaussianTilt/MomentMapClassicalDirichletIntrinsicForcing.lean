import GaussianTilt.MomentMapClassicalDirichletIntrinsicCoefficientBounds
import GaussianTilt.MomentMapClassicalDirichletTangentialForcingCalculus

/-! # Genuine interior coefficient and forcing fields for intrinsic jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

def intrinsicTangentSource {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (F β : CoordinateSpace n → ℝ) (a l : Fin n)
    (x : CoordinateSpace n) : ℝ :=
  coordinateDerivative a F x-β x*coordinateDerivative l F x-
    intrinsicDerivative hS α j l x*linearizedMA (intrinsicHessian hS α j x)⁻¹ β x-
      2*coordinateDerivative l β x

lemma intrinsic_local_representative_coefficient_source
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {F β : CoordinateSpace n → ℝ}
    (hMA : ∀ y ∈ interior S, (intrinsicHessian hS α j y).det = Real.exp (F y))
    {x : CoordinateSpace n} (hx : x ∈ interior S) (a l : Fin n) :
    ∃ u : CoordinateSpace n → ℝ, ContDiff ℝ ∞ u ∧
      (∀ i, intrinsicDerivative hS α j i =ᶠ[𝓝 x] coordinateDerivative i u) ∧
      intrinsicHessian hS α j =ᶠ[𝓝 x] coordinateHessian u ∧
      (fun y => (intrinsicHessian hS α j y)⁻¹) =ᶠ[𝓝 x] variableInverseHessian u F ∧
      intrinsicTangentSource hS α j F β a l =ᶠ[𝓝 x]
        tangentialFieldForcing (variableInverseHessian u F) u F β a l := by
  obtain ⟨u,hu,he,hDu,hHu⟩ := intrinsic_exists_smooth_representative_at hS hα j hs hx
  have hAeq : (fun y => (intrinsicHessian hS α j y)⁻¹) =ᶠ[𝓝 x] variableInverseHessian u F := by
    filter_upwards [isOpen_interior.mem_nhds hx,hHu] with y hy hH
    rw [variableInverseHessian_eq_inverse (by rw [← hH]; exact hMA y hy),hH]
  refine ⟨u,hu,hDu,hHu,hAeq,?_⟩
  filter_upwards [hDu l,hAeq] with y hy hA
  simp only [intrinsicTangentSource,tangentialFieldForcing,hy,hA]

lemma contDiffOn_intrinsicInverseHessian
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {F : CoordinateSpace n → ℝ} (hF : ContDiff ℝ ∞ F)
    (hMA : ∀ y ∈ interior S, (intrinsicHessian hS α j y).det = Real.exp (F y)) (i l : Fin n) :
    ContDiffOn ℝ ∞ (fun x => (intrinsicHessian hS α j x)⁻¹ i l) (interior S) := by
  intro x hx
  obtain ⟨u,hu,hDu,hHu,hA,hsource⟩ := intrinsic_local_representative_coefficient_source hS hα j hs
    (β := fun _ => 0) hMA hx i l
  exact ((smooth_variableInverseHessian hu hF i l).contDiffAt.congr_of_eventuallyEq
    (hA.mono (fun y hy => congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i l) hy))).contDiffWithinAt

lemma contDiffOn_intrinsicTangentSource
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {F β : CoordinateSpace n → ℝ} (hF : ContDiff ℝ ∞ F) (hβ : ContDiff ℝ ∞ β)
    (hMA : ∀ y ∈ interior S, (intrinsicHessian hS α j y).det = Real.exp (F y)) (a l : Fin n) :
    ContDiffOn ℝ ∞ (intrinsicTangentSource hS α j F β a l) (interior S) := by
  intro x hx
  obtain ⟨u,hu,hDu,hHu,hA,hsource⟩ := intrinsic_local_representative_coefficient_source hS hα j hs hMA hx a l
  exact ((contDiff_tangentialFieldForcing hu hF hβ (smooth_variableInverseHessian hu hF) a l).contDiffAt.congr_of_eventuallyEq hsource).contDiffWithinAt

/-- The true tangential field satisfies the actual scalar elliptic equation
on the interior, with precisely the intrinsic source term used above. -/
theorem intrinsic_tangent_field_equation
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {F β : CoordinateSpace n → ℝ}
    (hMA : ∀ y ∈ interior S, (intrinsicHessian hS α j y).det = Real.exp (F y))
    {x : CoordinateSpace n} (hx : x ∈ interior S) (hp : (intrinsicHessian hS α j x).PosDef)
    (hβ : ContDiffAt ℝ 2 β x) (a l : Fin n) :
    linearizedMA (intrinsicHessian hS α j x)⁻¹ (intrinsicTangentField hS α j β a l) x =
      intrinsicTangentSource hS α j F β a l x := by
  obtain ⟨u,hu,he,hDu,hHu⟩ := intrinsic_exists_smooth_representative_at hS hα j hs hx
  have hnear : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx,hHu] with y hy hey
    rw [← hey]
    exact hMA y hy
  have hTeq : intrinsicTangentField hS α j β a l =ᶠ[𝓝 x]
      (fun y => coordinateDerivative a u y-β y*coordinateDerivative l u y) := by
    filter_upwards [hDu a,hDu l] with y ha hl
    simp only [intrinsicTangentField,ha,hl]
  rw [hHu.self_of_nhds] at hp
  unfold intrinsicTangentSource
  rw [hHu.self_of_nhds,(hDu l).self_of_nhds]
  have hleft : linearizedMA (coordinateHessian u x)⁻¹ (intrinsicTangentField hS α j β a l) x =
      linearizedMA (coordinateHessian u x)⁻¹ (fun y => coordinateDerivative a u y-β y*coordinateDerivative l u y) x := by
    unfold linearizedMA
    rw [coordinateHessian_congr_nhds hTeq]
  rw [hleft,linearizedMA_tangential_derivative hu hβ hp hnear]

end GaussianTilt.MomentMapRegularity
