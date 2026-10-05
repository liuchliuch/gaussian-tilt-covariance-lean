import GaussianTilt.MomentMapLinearDirichletHarmonicL2Regularity
import GaussianTilt.MomentMapLinearDirichletClassicalEquation

/-!
# Localized distributional harmonic regularity

An actual compact smooth cutoff removes the artificial global support
condition. Only a bound on the original harmonic domain is needed; local
bounds can be used by shrinking that domain. The canonical representative
therefore becomes smooth throughout the open harmonic region.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Genuine local Weyl regularity for arbitrary L² data. No pointwise bound or compact support is assumed. -/
theorem exists_local_smooth_rep_of_L2_distribution_harmonic [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {f : KernelSpace n → ℝ}
    (hf : MemLp f 2 volume)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, f y * kernelLaplacian ψ y) = 0)
    {x₀ : KernelSpace n} (hx₀ : x₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : KernelSpace n → ℝ, ContDiff ℝ ∞ v ∧
      ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ r → v x = f x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  let χ : ContDiffBump x₀ := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let g := fun y => χ y * f y
  have hgi : MemLp g 2 volume := by
    apply hf.norm.mono' (χ.continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    apply ae_of_all
    intro y
    change ‖χ y*f y‖ ≤ ‖f y‖
    rw [norm_mul,Real.norm_of_nonneg χ.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) χ.le_one
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mul_right
  have hgeq : ∀ y ∈ Metric.ball x₀ (R / 4), g y = f y := by
    intro y hy
    change χ y * f y = _
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]
  have hgdist : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball x₀ (R / 4) → (∫ y, g y * kernelLaplacian ψ y) = 0 := by
    intro ψ hψ hψc hψs
    have he := heq ψ hψ hψc
      (hψs.trans ((Metric.ball_subset_ball (by linarith : R / 4 ≤ R)).trans hRΩ))
    rw [← he]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by
      dsimp only
      by_cases hy : y ∈ tsupport ψ
      · rw [hgeq y (hψs hy)]
      · rw [kernelLaplacian_zero_off_tsupport ψ hy, mul_zero, mul_zero])
  obtain ⟨r, hr, v, hv, hvg⟩ := exists_local_smooth_rep_of_compact_L2_distribution_harmonic Metric.isOpen_ball hgi hgc
    hgdist (Metric.mem_ball_self (by positivity : 0 < R / 4))
  refine ⟨min r (R / 4), lt_min hr (by positivity), v, hv, ?_⟩
  filter_upwards [hvg] with y hy hym
  have hyr := Metric.ball_subset_ball (min_le_left r (R / 4)) hym
  have hyR := Metric.ball_subset_ball (min_le_right r (R / 4)) hym
  exact (hy hyr).trans (hgeq y hyR)

/-- A single actual AE representative is smooth on the harmonic
region; local mollifier limits perform the patching. -/
theorem harmonicRepresentative_contDiffAt_of_L2_distribution_harmonic [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {f : KernelSpace n → ℝ}
    (hf : MemLp f 2 volume)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, f y * kernelLaplacian ψ y) = 0) :
    ∀ x ∈ Ω, ContDiffAt ℝ ∞ (harmonicRepresentative f) x :=
  contDiffAt_harmonicRepresentative_of_local_representatives
    (fun _ hx => exists_local_smooth_rep_of_L2_distribution_harmonic hΩ hf heq hx)

/-- The constructed L² representative satisfies the ordinary harmonic
PDE, rather than only its distributional version. -/
theorem harmonicRepresentative_laplacian_of_L2_distribution_harmonic [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {f : KernelSpace n → ℝ}
    (hf : MemLp f 2 volume)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, f y * kernelLaplacian ψ y)=0) :
    ∀ x ∈ Ω, kernelLaplacian (harmonicRepresentative f) x=0 := by
  apply harmonicRepresentative_laplacian_of_local_representatives hΩ continuous_const
  · intro x hx
    obtain ⟨r,hr,v,hv,he⟩ := exists_local_smooth_rep_of_L2_distribution_harmonic hΩ hf heq hx
    exact ⟨r,hr,v,contDiff_infty.mp hv 2,he⟩
  · intro ψ hψ hψc hψΩ
    simpa only [zero_mul,integral_zero] using heq ψ hψ hψc hψΩ

end GaussianTilt.MomentMapLinearDirichlet
