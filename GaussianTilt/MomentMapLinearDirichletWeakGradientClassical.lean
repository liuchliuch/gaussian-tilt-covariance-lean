import GaussianTilt.MomentMapLinearDirichletWeakGradientClassicalGlobal
import GaussianTilt.MomentMapHolderInteriorEmbedding

/-! # Genuine local C¹ regularity from a continuous distributional gradient -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma weakGradient_test_derivative_zero_off_support (ψ : KernelSpace n → ℝ)
    {x : KernelSpace n} (hx : x ∉ tsupport ψ) (v : KernelSpace n) :
    kernelDirectionalDerivative v ψ x=0 := by
  have he := (notMem_tsupport_iff_eventuallyEq.mp hx).fderiv_eq (𝕜 := ℝ)
  unfold kernelDirectionalDerivative
  rw [he]
  simp

/-- Only local continuity and literal compact-test integration by parts
are required. Compact cutoffs construct globally continuous auxiliary
fields, so no global integrability or extension hypothesis is added. -/
theorem hasFDerivAt_of_continuous_weak_gradient
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {u : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    (hu : ContinuousOn u Ω) (hD : ContinuousOn D Ω)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y))
    {x₀ : KernelSpace n} (hx₀ : x₀ ∈ Ω) : HasFDerivAt u (D x₀) x₀ := by
  obtain ⟨R,hR,hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  let χ : ContDiffBump x₀ := ⟨R/4,R/2,by positivity,by linarith⟩
  let v := fun y => χ y*u y
  let E := fun y => χ y • D y
  have hχs : tsupport (χ : KernelSpace n → ℝ) ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by change R/2<R; linarith)).trans hRΩ
  have hvc : Continuous v := by
    apply continuous_iff_continuousAt.mpr
    intro y
    by_cases hy : y ∈ Ω
    · exact χ.continuous.continuousAt.mul (hu.continuousAt (hΩ.mem_nhds hy))
    · have hyc : y ∉ tsupport (χ : KernelSpace n → ℝ) := fun h => hy (hχs h)
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyc] with z hz
      change χ z*u z=0
      simp only [hz,Pi.zero_apply,zero_mul]
  have hEc : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro y
    by_cases hy : y ∈ Ω
    · exact χ.continuous.continuousAt.smul (hD.continuousAt (hΩ.mem_nhds hy))
    · have hyc : y ∉ tsupport (χ : KernelSpace n → ℝ) := fun h => hy (hχs h)
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyc] with z hz
      change χ z • D z=0
      simp only [hz,Pi.zero_apply,zero_smul]
  have hχone (y : KernelSpace n) (hy : y ∈ Metric.ball x₀ (R/4)) : χ y=1 :=
    χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have htest : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball x₀ (R/4) →
      (∫ y, v y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, E y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y) := by
    intro i ψ hψ hψc hψs
    have he := hweak i ψ hψ hψc (hψs.trans ((Metric.ball_subset_ball (by linarith : R/4 ≤ R)).trans hRΩ))
    calc
      _ = ∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y := by
        apply integral_congr_ae
        apply ae_of_all
        intro y
        dsimp only
        by_cases hy : y ∈ tsupport ψ
        · simp only [v,hχone y (hψs hy),one_mul]
        · rw [weakGradient_test_derivative_zero_off_support ψ hy,mul_zero,mul_zero]
      _ = -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y) := he
      _ = _ := by
        congr 1
        apply integral_congr_ae
        apply ae_of_all
        intro y
        dsimp only
        by_cases hy : y ∈ tsupport ψ
        · simp only [E,hχone y (hψs hy),one_smul]
        · rw [image_eq_zero_of_notMem_tsupport hy,mul_zero,mul_zero]
  have hv := hasFDerivAt_of_continuous_weak_gradient_global Metric.isOpen_ball hvc hEc htest
    (Metric.mem_ball_self (by positivity : 0 < R/4))
  have hE0 : E x₀=D x₀ := by simp only [E,hχone x₀ (Metric.mem_ball_self (by positivity : 0<R/4)),one_smul]
  rw [hE0] at hv
  apply hv.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x₀ (by positivity : 0 < R/4)] with y hy
  simp only [v,hχone y hy,one_mul]

/-- A continuous weak gradient is the actual continuous classical gradient
throughout the open domain. -/
theorem contDiffOn_one_of_continuous_weak_gradient
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {u : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    (hu : ContinuousOn u Ω) (hD : ContinuousOn D Ω)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y)) :
    ContDiffOn ℝ 1 u Ω := by
  have hd (x : KernelSpace n) (hx : x ∈ Ω) := hasFDerivAt_of_continuous_weak_gradient hΩ hu hD hweak hx
  rw [show (1:WithTop ℕ∞)=0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  exact hD.congr (fun x hx => (hd x hx).fderiv)

/-- The same true gradient extends to the convex closed boundary in the
within-domain sense by the proved segment/closure derivative theorem. -/
theorem hasFDerivWithinAt_of_continuous_weak_gradient
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {u : KernelSpace n → ℝ} {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    (hu : ContinuousOn u S) (hD : ContinuousOn D S)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior S →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y))
    {x : KernelSpace n} (hx : x ∈ S) : HasFDerivWithinAt u (D x) S x :=
  GaussianTilt.HolderSpace.hasFDerivWithinAt_of_continuous_interior_field hS hSc hint hu hD
    (fun y hy => hasFDerivAt_of_continuous_weak_gradient isOpen_interior
      (hu.mono interior_subset) (hD.mono interior_subset) hweak hy) hx

end GaussianTilt.MomentMapLinearDirichlet
