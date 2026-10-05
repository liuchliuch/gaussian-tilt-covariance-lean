import GaussianTilt.MomentMapLinearDirichletWeakGradientClassical

/-! # Vector-gradient and almost-everywhere representative interfaces -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Vector form of the actual weak-gradient-to-classical derivative
 theorem. The Euclidean covector is explicitly `innerSL` of the field. -/
theorem hasFDerivAt_of_continuous_weak_gradient_vector
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {u : KernelSpace n → ℝ}
    {G : KernelSpace n → KernelSpace n} (hu : ContinuousOn u Ω) (hG : ContinuousOn G Ω)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, G y i*ψ y))
    {x : KernelSpace n} (hx : x ∈ Ω) : HasFDerivAt u (innerSL ℝ (G x)) x := by
  apply hasFDerivAt_of_continuous_weak_gradient hΩ hu ((innerSL ℝ).continuous.comp_continuousOn hG) _ hx
  intro i ψ hψ hψc hψs
  simpa only [Function.comp_apply,innerSL_apply,EuclideanSpace.inner_basisFun_real] using hweak i ψ hψ hψc hψs

theorem contDiffOn_one_of_continuous_weak_gradient_vector
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {u : KernelSpace n → ℝ}
    {G : KernelSpace n → KernelSpace n} (hu : ContinuousOn u Ω) (hG : ContinuousOn G Ω)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, G y i*ψ y)) : ContDiffOn ℝ 1 u Ω := by
  apply contDiffOn_one_of_continuous_weak_gradient hΩ hu ((innerSL ℝ).continuous.comp_continuousOn hG)
  intro i ψ hψ hψc hψs
  simpa only [Function.comp_apply,innerSL_apply,EuclideanSpace.inner_basisFun_real] using hweak i ψ hψ hψc hψs

/-- The continuous field obtained from genuine Campanato representative
construction transfers the weak identity by its actual AE equality. -/
theorem classical_gradient_of_continuous_ae_weak_gradient
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {u : KernelSpace n → ℝ}
    {G W : KernelSpace n → KernelSpace n} (hu : ContinuousOn u Ω) (hG : ContinuousOn G Ω)
    (hGW : ∀ᵐ y ∂volume, y ∈ Ω → G y=W y)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, W y i*ψ y)) :
    ContDiffOn ℝ 1 u Ω ∧ ∀ x ∈ Ω, HasFDerivAt u (innerSL ℝ (G x)) x := by
  have heq : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, G y i*ψ y) := by
    intro i ψ hψ hψc hψs
    rw [hweak i ψ hψ hψc hψs]
    congr 1
    apply integral_congr_ae
    filter_upwards [hGW] with y hy
    by_cases hys : y ∈ tsupport ψ
    · rw [hy (hψs hys)]
    · rw [image_eq_zero_of_notMem_tsupport hys,mul_zero,mul_zero]
  exact ⟨contDiffOn_one_of_continuous_weak_gradient_vector hΩ hu hG heq,
    fun x hx => hasFDerivAt_of_continuous_weak_gradient_vector hΩ hu hG heq hx⟩

theorem hasFDerivWithinAt_of_continuous_weak_gradient_vector
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {u : KernelSpace n → ℝ} {G : KernelSpace n → KernelSpace n}
    (hu : ContinuousOn u S) (hG : ContinuousOn G S)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior S →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, G y i*ψ y))
    {x : KernelSpace n} (hx : x ∈ S) : HasFDerivWithinAt u (innerSL ℝ (G x)) S x := by
  apply hasFDerivWithinAt_of_continuous_weak_gradient hS hSc hint hu
    ((innerSL ℝ).continuous.comp_continuousOn hG) _ hx
  intro i ψ hψ hψc hψs
  simpa only [Function.comp_apply,innerSL_apply,EuclideanSpace.inner_basisFun_real] using hweak i ψ hψ hψc hψs

end GaussianTilt.MomentMapLinearDirichlet
