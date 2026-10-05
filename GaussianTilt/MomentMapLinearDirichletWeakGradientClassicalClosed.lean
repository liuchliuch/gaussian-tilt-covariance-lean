import GaussianTilt.MomentMapLinearDirichletWeakGradientClassicalVector

/-! # Actual closed-domain C¹ regularity from continuous weak gradients -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The continuous weak covector is also the true within derivative on the
boundary, and yields C¹ on the whole closed convex domain. -/
theorem contDiffOn_one_closed_of_continuous_weak_gradient
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {u : KernelSpace n → ℝ} {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    (hu : ContinuousOn u S) (hD : ContinuousOn D S)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior S →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y)) : ContDiffOn ℝ 1 u S := by
  have hd (x : KernelSpace n) (hx : x ∈ S) := hasFDerivWithinAt_of_continuous_weak_gradient hS hSc hint hu hD hweak hx
  have hUD : UniqueDiffOn ℝ S := uniqueDiffOn_convex hS hint
  rw [show (1:WithTop ℕ∞)=0+1 from rfl,contDiffOn_succ_iff_fderivWithin hUD]
  refine ⟨fun x hx => (hd x hx).differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  exact hD.congr (fun x hx => (hd x hx).fderivWithin (hUD x hx))

theorem contDiffOn_one_closed_of_continuous_weak_gradient_vector
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {u : KernelSpace n → ℝ} {G : KernelSpace n → KernelSpace n}
    (hu : ContinuousOn u S) (hG : ContinuousOn G S)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior S →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, G y i*ψ y)) : ContDiffOn ℝ 1 u S := by
  apply contDiffOn_one_closed_of_continuous_weak_gradient hS hSc hint hu
    ((innerSL ℝ).continuous.comp_continuousOn hG)
  intro i ψ hψ hψc hψs
  simpa only [Function.comp_apply,innerSL_apply,EuclideanSpace.inner_basisFun_real] using hweak i ψ hψ hψc hψs

end GaussianTilt.MomentMapLinearDirichlet
