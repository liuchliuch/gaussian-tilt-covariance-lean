import GaussianTilt.MomentMapLinearDirichletHarmonicPatch

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

lemma kernelLaplacian_zero_off_tsupport (ψ : KernelSpace n → ℝ)
    {x : KernelSpace n} (hx : x ∉ tsupport ψ) : kernelLaplacian ψ x = 0 := by
  have he := kernelLaplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hx)
  simpa [kernelLaplacian, directionalHessian] using he

/-- Local boundedness on the domain suffices; no global boundedness or
compact support is assumed of the original function. -/
theorem exists_local_smooth_rep_of_bounded_distribution_harmonic [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {f : KernelSpace n → ℝ}
    (hf : LocallyIntegrable f volume) {B : ℝ} (hfB : ∀ x ∈ Ω, |f x| ≤ B)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, f y * kernelLaplacian ψ y) = 0)
    {x₀ : KernelSpace n} (hx₀ : x₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : KernelSpace n → ℝ, ContDiff ℝ ∞ v ∧
      ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ r → v x = f x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  let χ : ContDiffBump x₀ := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let g := fun y => χ y * f y
  have hgi : LocallyIntegrable g volume :=
    (hf.integrable_smul_left_of_hasCompactSupport χ.continuous χ.hasCompactSupport).locallyIntegrable
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mul_right
  have hgB : ∀ y, |g y| ≤ max B 0 := by
    intro y
    by_cases hy : χ y = 0
    · simp only [g, hy, zero_mul, abs_zero]
      exact le_max_right _ _
    · have hyR : y ∈ Metric.ball x₀ (R / 2) := by
        have hs : y ∈ Function.support (χ : KernelSpace n → ℝ) := hy
        rwa [χ.support_eq] at hs
      have hyΩ := hRΩ (Metric.ball_subset_ball (by linarith : R / 2 ≤ R) hyR)
      change |χ y * f y| ≤ _
      rw [abs_mul, abs_of_nonneg χ.nonneg]
      calc
        χ y * |f y| ≤ 1 * |f y| := mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)
        _ = |f y| := one_mul _
        _ ≤ B := hfB y hyΩ
        _ ≤ max B 0 := le_max_left _ _
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
  obtain ⟨r, hr, v, hv, hvg⟩ := exists_local_smooth_rep_of_distribution_harmonic Metric.isOpen_ball hgi hgc hgB
    hgdist (Metric.mem_ball_self (by positivity : 0 < R / 4))
  refine ⟨min r (R / 4), lt_min hr (by positivity), v, hv, ?_⟩
  filter_upwards [hvg] with y hy hym
  have hyr := Metric.ball_subset_ball (min_le_left r (R / 4)) hym
  have hyR := Metric.ball_subset_ball (min_le_right r (R / 4)) hym
  exact (hy hyr).trans (hgeq y hyR)

/-- A single actual AE representative is smooth on the bounded harmonic
region; local mollifier limits perform the patching. -/
theorem harmonicRepresentative_contDiffAt_of_distribution_harmonic [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {f : KernelSpace n → ℝ}
    (hf : LocallyIntegrable f volume) {B : ℝ} (hfB : ∀ x ∈ Ω, |f x| ≤ B)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, f y * kernelLaplacian ψ y) = 0) :
    ∀ x ∈ Ω, ContDiffAt ℝ ∞ (harmonicRepresentative f) x :=
  contDiffAt_harmonicRepresentative_of_local_representatives
    (fun _ hx => exists_local_smooth_rep_of_bounded_distribution_harmonic hΩ hf hfB heq hx)

end GaussianTilt.MomentMapLinearDirichlet
