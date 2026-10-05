import GaussianTilt.MomentMapLinearDirichletCampanatoL2Interpolation
import GaussianTilt.MomentMapLinearDirichletWeakGradientClassicalVector

/-! # Genuine weak-gradient Campanato estimates imply actual C¹ regularity -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The full weak-to-classical first-order bridge: genuine local L²
Campanato estimates construct the continuous gradient field and the
literal weak identity then proves that it is the actual derivative. -/
theorem classical_gradient_of_local_l2_campanato [NeZero n]
    (j : Fin n) (u : KernelSpace n → ℝ) (W : KernelSpace n → KernelSpace n)
    {R ρ C α : ℝ}
    (hW : MemLp W 2 (volume.restrict (upperCampanatoBall j 0 (2*R))))
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hα : 0 < α)
    (hu : ContinuousOn u (upperCampanatoBall j 0 (R/4)))
    (hApprox : ∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j → ∀ k : ℕ, ∃ q : KernelSpace n,
      (∫ z in upperCampanatoBall j x (R*ρ^k), ‖W z-q‖^2) ≤ C*(R*ρ^k)^((n:ℝ)+2*α))
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperCampanatoBall j 0 (R/4) →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, W y i*ψ y)) :
    ∃ G : KernelSpace n → KernelSpace n,
      ContinuousOn G (Metric.closedBall 0 (R/4) ∩ {x | 0 ≤ x j}) ∧
      (∀ᵐ x ∂volume, ‖x‖ ≤ R/4 → 0 < x j → G x = W x) ∧
      (∀ x : KernelSpace n, ‖x‖ ≤ R/4 → 0 ≤ x j →
        ∀ y : KernelSpace n, ‖y‖ ≤ R/4 → 0 ≤ y j →
          ‖G x-G y‖ ≤ campanatoL2HolderConstant n (C*ρ^(-((n:ℝ)+2*α))) α*‖x-y‖^α) ∧
      ContDiffOn ℝ 1 u (upperCampanatoBall j 0 (R/4)) ∧
      (∀ x ∈ upperCampanatoBall j 0 (R/4), HasFDerivAt u (innerSL ℝ (G x)) x) := by
  obtain ⟨G,hGc,hAE,hHolder⟩ := exists_holder_representative_of_geometric_l2_campanato
    j W hW hR hρ hρ1 hC hα hApprox
  have hsub : upperCampanatoBall j 0 (R/4) ⊆
      Metric.closedBall 0 (R/4) ∩ {x : KernelSpace n | 0 ≤ x j} :=
    fun x hx => ⟨Metric.ball_subset_closedBall hx.1,show 0 ≤ x j from hx.2.le⟩
  have hAE' : ∀ᵐ x ∂volume, x ∈ upperCampanatoBall j 0 (R/4) → G x = W x := by
    filter_upwards [hAE] with x hx
    intro hxΩ
    have hn : ‖x‖ < R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hxΩ.1
    exact hx hn.le hxΩ.2
  obtain ⟨hC1,hD⟩ := classical_gradient_of_continuous_ae_weak_gradient
    (isOpen_upperCampanatoBall j 0 (R/4)) hu (hGc.mono hsub) hAE' hweak
  exact ⟨G,hGc,hAE,hHolder,hC1,hD⟩

end GaussianTilt.MomentMapLinearDirichlet
