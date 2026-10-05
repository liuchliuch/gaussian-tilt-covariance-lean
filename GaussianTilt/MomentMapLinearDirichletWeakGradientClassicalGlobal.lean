import GaussianTilt.MomentMapLinearDirichletWeakGradientClassicalMollification

/-! # Continuous weak covectors are genuine classical first derivatives -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The local test identity yields true differentiability by genuine
mollification, locally uniform convergence of the derivative field, and
the actual uniform-limit differentiation theorem. -/
theorem hasFDerivAt_of_continuous_weak_gradient_global
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {u : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    (hu : Continuous u) (hD : Continuous D)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y))
    {x₀ : KernelSpace n} (hx₀ : x₀ ∈ Ω) : HasFDerivAt u (D x₀) x₀ := by
  apply hasFDerivAt_of_tendstoUniformlyOnFilter (f := fun k => harmonicMollify k u)
    ((tendstoLocallyUniformly_iff_filter.mp (weakGradientMollify_tendstoLocallyUniformly hD)) x₀)
  · obtain ⟨R,hR,hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
    have hk : ∀ᶠ k : ℕ in atTop, (harmonicMollifierBump n k).rOut < R/2 :=
      (tendsto_order.mp harmonicMollifier_radius_tendsto).2 _ (half_pos hR)
    have hy : ∀ᶠ y in 𝓝 x₀, y ∈ Metric.ball x₀ (R/2) := Metric.ball_mem_nhds x₀ (half_pos hR)
    filter_upwards [hk.prod_mk hy] with p hp
    apply harmonicMollify_hasFDerivAt_of_weak_gradient hu hD hweak p.1 p.2
    intro z hz
    have hzy := harmonic_mollifier_translated_support p.1 p.2 hz
    apply hRΩ
    have hrad : dist z p.2 ≤ (harmonicMollifierBump n p.1).rOut := hzy
    have hyx : dist p.2 x₀ < R/2 := hp.2
    change dist z x₀ < R
    linarith [dist_triangle z p.2 x₀,hp.1]
  · apply Eventually.of_forall
    intro y
    exact ContDiffBump.convolution_tendsto_right_of_continuous (φ := harmonicMollifierBump n) harmonicMollifier_radius_tendsto hu y

 theorem contDiffOn_one_of_continuous_weak_gradient_global
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {u : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    (hu : Continuous u) (hD : Continuous D)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y)) :
    ContDiffOn ℝ 1 u Ω := by
  have hd (x : KernelSpace n) (hx : x ∈ Ω) := hasFDerivAt_of_continuous_weak_gradient_global hΩ hu hD hweak hx
  rw [show (1:WithTop ℕ∞)=0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  exact hD.continuousOn.congr (fun x hx => (hd x hx).fderiv)

end GaussianTilt.MomentMapLinearDirichlet
