import GaussianTilt.MomentMapLinearDirichletHarmonicL2Limit

/-!
# Genuine local smoothness of a distribution-harmonic function

The actual mollifiers solve the ordinary harmonic equation on interior
balls. The proved compact Newtonian smoothing kernel reproduces them, and
dominated convergence yields a smooth representative of the original
function. All harmonic approximations and smoothing identities are built
here, rather than supplied as regularity assumptions.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A compactly supported L² function satisfying
the literal distributional harmonic equation has an actual smooth
representative near every interior point. -/
theorem exists_local_smooth_rep_of_compact_L2_distribution_harmonic [NeZero n]
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) {f : KernelSpace n → ℝ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, f y * kernelLaplacian ψ y) = 0)
    {x₀ : KernelSpace n} (hx₀ : x₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : KernelSpace n → ℝ, ContDiff ℝ ∞ v ∧
      ∀ᵐ x ∂volume, x ∈ Metric.ball x₀ r → v x = f x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  let r := R / 4
  have hr : 0 < r := div_pos hR (by norm_num)
  let χ : ContDiffBump (0 : KernelSpace n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hχ0 : (χ : KernelSpace n → ℝ) =ᶠ[𝓝 0] (fun _ => 1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : KernelSpace n) (half_pos hr)] with y hy
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hχs (y : KernelSpace n) (hy : y ∈ tsupport (χ : KernelSpace n → ℝ)) : ‖y‖ ≤ r := by
    rw [χ.tsupport_eq] at hy
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have happrox : ∀ x ∈ Metric.ball x₀ r, ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ tsupport (χ : KernelSpace n → ℝ), kernelLaplacian (harmonicMollify k f) (y+x) = 0 := by
    intro x hx
    have ht : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    filter_upwards [(tendsto_order.mp ht).2 r hr] with k hk
    intro y hy
    apply convolution_harmonic_of_distribution (hf.locallyIntegrable (by norm_num)) (harmonicMollifierBump n k).contDiff_normed
      (harmonicMollifierBump n k).hasCompactSupport_normed heq (y+x)
    apply (harmonic_mollifier_translated_support k (y+x)).trans
    intro z hz
    apply hRΩ
    have hx' : ‖x-x₀‖ < r := hx
    have hz' : ‖z-(y+x)‖ ≤ ((k : ℝ) + 1)⁻¹ := hz
    have hy' := hχs y hy
    have ht1 : ‖z-x₀‖ ≤ ‖z-(y+x)‖ + ‖(y+x)-x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have ht2 : ‖(y+x)-x₀‖ ≤ ‖y‖ + ‖x-x₀‖ := by
      rw [add_sub_assoc]
      exact norm_add_le _ _
    change ‖z-x₀‖ < R
    dsimp [r] at *
    linarith
  obtain ⟨v, hv, hvf⟩ := exists_smooth_rep_of_L2_harmonic_approximation χ.contDiff χ.hasCompactSupport hχ0 hf
    (fun k => contDiff_infty.mp (harmonicMollify_smooth (hf.locallyIntegrable (by norm_num)) k) 2)
    (harmonicMollify_compact hfc) (harmonicMollify_memLp hf) (integral_harmonicMollify_sub_sq_tendsto hf)
    (harmonicMollify_ae_tendsto (hf.locallyIntegrable (by norm_num))) happrox
  exact ⟨r, hr, v, hv, hvf⟩

end GaussianTilt.MomentMapLinearDirichlet
