import GaussianTilt.MomentMapClassicalDirichletIntrinsicTangentBounds
import GaussianTilt.MomentMapClassicalDirichletMixedBounds

/-! # Actual mixed-field calculus for intrinsic Hölder jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

def intrinsicTangentField {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (β : CoordinateSpace n → ℝ) (a l : Fin n) : CoordinateSpace n → ℝ :=
  fun x => intrinsicDerivative hS α j a x - β x*intrinsicDerivative hS α j l x

def intrinsicTangentDifferential {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (β : CoordinateSpace n → ℝ) (a l : Fin n)
    (x : CoordinateSpace n) : CoordinateSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1)).comp (intrinsicSecond hS α j x) -
    (β x • (ContinuousLinearMap.apply ℝ ℝ (Pi.single l 1)).comp (intrinsicSecond hS α j x) +
      intrinsicDerivative hS α j l x • fderiv ℝ β x)

lemma intrinsicDerivative_hasFDerivWithinAt
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) {x : CoordinateSpace n} (hx : x ∈ S) (i : Fin n) :
    HasFDerivWithinAt (intrinsicDerivative hS α j i)
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).comp (intrinsicSecond hS α j x)) S x := by
  let L : (CoordinateSpace n →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)
  exact L.hasFDerivAt.comp_hasFDerivWithinAt x (jet_first_hasFDerivWithinAt hS hα j hx)

lemma intrinsicTangentField_hasFDerivWithinAt
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) {x : CoordinateSpace n} (hx : x ∈ S)
    {β : CoordinateSpace n → ℝ} (hβ : DifferentiableAt ℝ β x) (a l : Fin n) :
    HasFDerivWithinAt (intrinsicTangentField hS α j β a l)
      (intrinsicTangentDifferential hS α j β a l x) S x :=
  (intrinsicDerivative_hasFDerivWithinAt hS hα j hx a).sub
    (hβ.hasFDerivAt.hasFDerivWithinAt.mul (intrinsicDerivative_hasFDerivWithinAt hS hα j hx l))

lemma intrinsicTangentDifferential_apply_coordinate
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (β : CoordinateSpace n → ℝ)
    (a l k : Fin n) (x : CoordinateSpace n) :
    intrinsicTangentDifferential hS α j β a l x (Pi.single k 1) =
      intrinsicHessian hS α j x a k - β x*intrinsicHessian hS α j x l k -
        coordinateDerivative k β x*intrinsicDerivative hS α j l x := by
  simp only [intrinsicTangentDifferential,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    smul_eq_mul,intrinsicHessian,coordinateDerivative]
  ring

/-- The real local tangential forcing estimate transfers through a genuine
interior smooth representative, leaving the boundary fields intrinsic. -/
theorem intrinsic_tangent_forcing_trace_bound [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S))
    {F β : CoordinateSpace n → ℝ}
    (hMA : ∀ y ∈ interior S, (intrinsicHessian hS α j y).det = Real.exp (F y))
    {x : CoordinateSpace n} (hx : x ∈ interior S) (hβ : ContDiffAt ℝ 2 β x)
    (hp : (intrinsicHessian hS α j x).PosDef) (a l : Fin n)
    {G B₀ B₁ B₂ K D : ℝ} (hG : 0 ≤ G) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hK : 0 ≤ K)
    (hg : |intrinsicDerivative hS α j l x| ≤ G) (hβ0 : |β x| ≤ B₀)
    (hβ1 : |coordinateDerivative l β x| ≤ B₁) (hβ2 : ∀ i k, |coordinateHessian β x i k| ≤ B₂)
    (hFa : |coordinateDerivative a F x| ≤ K) (hFl : |coordinateDerivative l F x| ≤ K)
    (hdet : (intrinsicHessian hS α j x).det ≤ D) :
    |linearizedMA (intrinsicHessian hS α j x)⁻¹ (intrinsicTangentField hS α j β a l) x| ≤
      ((K+B₀*K+2*B₁)*max 1 D+G*(n:ℝ)^2*B₂)*(intrinsicHessian hS α j x)⁻¹.trace := by
  obtain ⟨u,hu,he,hDu,hHu⟩ := intrinsic_exists_smooth_representative_at hS hα j hs hx
  have hnear : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx,hHu] with y hy hey
    rw [← hey]
    exact hMA y hy
  have hTeq : intrinsicTangentField hS α j β a l =ᶠ[𝓝 x]
      (fun y => coordinateDerivative a u y-β y*coordinateDerivative l u y) := by
    filter_upwards [hDu a,hDu l] with y ha hl
    simp only [intrinsicTangentField,ha,hl]
  rw [hHu.self_of_nhds] at hp hdet ⊢
  rw [(hDu l).self_of_nhds] at hg
  unfold linearizedMA
  rw [coordinateHessian_congr_nhds hTeq]
  exact tangential_derivative_forcing_trace_bound hu hβ hp hnear a l hG hB₀ hB₁ hB₂ hK
    hg hβ0 hβ1 hβ2 hFa hFl hdet

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

lemma intrinsic_tangent_field_zero {α a₀ b₀ : ℝ} (hα : 0 < α)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (p : BoundaryChartPatch d.coordinateDefining) {x : CoordinateSpace n}
    (hxp : x ∈ Metric.closedBall p.center p.radius) (hx0 : d.coordinateDefining x = 0)
    (hbar : ∀ y ∈ {z | d.coordinateDefining z ≤ 0},
      b₀*d.coordinateDefining y ≤ intrinsicValue d.coordinate_body_convex α j.1 y ∧
      intrinsicValue d.coordinate_body_convex α j.1 y ≤ a₀*d.coordinateDefining y) (a : Fin n) :
    intrinsicTangentField d.coordinate_body_convex α j.1
      (boundaryChartCoefficient d.coordinateDefining p.index a) a p.index x = 0 := by
  have hxb : x ∈ frontier {y | d.coordinateDefining y ≤ 0} := by rwa [d.coordinate_body_frontier]
  obtain ⟨lam,hla,hlb,hfirst,hsecond⟩ := d.intrinsic_boundary_jet_data hα j hxb hbar
  have he (i : Fin n) : intrinsicDerivative d.coordinate_body_convex α j.1 i x =
      lam*coordinateDerivative i d.coordinateDefining x :=
    congrArg (fun L : CoordinateSpace n →L[ℝ] ℝ => L (Pi.single i 1)) hfirst
  unfold intrinsicTangentField
  rw [he a,he p.index]
  unfold boundaryChartCoefficient
  have hk := p.derivative_ne_zero hxp
  field_simp
  <;> ring

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
