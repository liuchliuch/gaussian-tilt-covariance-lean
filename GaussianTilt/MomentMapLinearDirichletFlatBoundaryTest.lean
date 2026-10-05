import GaussianTilt.MomentMapLinearDirichletFlatLayerBound
import GaussianTilt.MomentMapLinearDirichletSmoothAbs

/-!
# Removing the flat boundary cutoff from the literal weak equation

Two genuine boundary zeros cancel the ε⁻² cutoff derivative. Uniform
integrable domination and eventual pointwise agreement justify the limit,
so a smooth test vanishing on the plane is admissible without assuming a
trace theorem or an integration-by-parts boundary identity.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The actual local weak harmonic identity extends to compact smooth
tests vanishing on the boundary plane, from a proved linear height bound. -/
theorem integral_mul_laplacian_flat_zero_test (j : Fin n) {u ψ : KernelSpace n → ℝ}
    (hu : LocallyIntegrable u volume) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hu0 : ∀ x, x j ≤ 0 → u x = 0)
    (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ C * |x j|)
    (heq : ∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R ∩ {x | 0 < x j} → (∫ x, u x * kernelLaplacian φ x) = 0)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψR : tsupport ψ ⊆ Metric.ball 0 R) (hψ0 : ∀ x, x j = 0 → ψ x = 0) :
    (∫ x, u x * kernelLaplacian ψ x) = 0 := by
  classical
  obtain ⟨D, M, hD, hM, hψg, hψd, hψlap⟩ := exists_flat_test_bounds j hψ hψc hψ0
  obtain ⟨M₁, M₂, hM₁, hM₂, hM₁b, hM₂b⟩ := exists_flatBoundaryStep_derivative_bounds
  let φ := fun k x => scaledFlatBoundaryStep (absRegularizationScale k) (x j) * ψ x
  have hφ (k : ℕ) : ContDiff ℝ ∞ (φ k) :=
    (contDiff_coordinate_profile (scaledFlatBoundaryStep_contDiff _) j).mul hψ
  have hφc (k : ℕ) : HasCompactSupport (φ k) := hψc.mul_left
  have hφs (k : ℕ) : tsupport (φ k) ⊆ tsupport ψ := tsupport_scaledFlatBoundaryStep_mul j
  have hφΩ (k : ℕ) : tsupport (φ k) ⊆ Metric.ball 0 R ∩ {x | 0 < x j} :=
    subset_inter ((hφs k).trans hψR)
      (tsupport_scaledFlatBoundaryStep_mul_positive (absRegularizationScale_pos k) ψ j)
  have hzero (k : ℕ) : (∫ x, u x * kernelLaplacian (φ k) x) = 0 := heq _ (hφ k) (hφc k) (hφΩ k)
  let A := C*R*M + 4*C*D*M₂ + 4*C*M₁*D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let bound := (tsupport ψ).indicator (fun _ : KernelSpace n => A)
  have hboundi : Integrable bound volume :=
    (integrableOn_const hψc.measure_lt_top.ne (by finiteness)).integrable_indicator hψc.measurableSet
  have hbound (k : ℕ) : ∀ᵐ x ∂volume, ‖u x * kernelLaplacian (φ k) x‖ ≤ bound x := by
    apply ae_of_all
    intro x
    by_cases hx : x ∈ tsupport ψ
    · rw [show bound x = A from indicator_of_mem hx _]
      rw [Real.norm_eq_abs]
      exact flat_boundary_layer_integrand_bound j hψ hC hD hM hM₁ hM₂ hR
        (absRegularizationScale_pos k) hu0 (fun y hy => hug y (hψR hy)) hψg hψd hψlap hM₁b hM₂b
        (fun y hy => (show |y j| ≤ ‖y‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y j).trans
          (show ‖y‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hψR hy).le) x hx
    · rw [show bound x = 0 from indicator_of_notMem hx _,
        kernelLaplacian_zero_off_tsupport (φ k) (fun hh => hx (hφs k hh)), mul_zero, norm_zero]
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun k => u x * kernelLaplacian (φ k) x) atTop
      (𝓝 (u x * kernelLaplacian ψ x)) := by
    apply ae_of_all
    intro x
    by_cases hx : x j ≤ 0
    · simp only [hu0 x hx, zero_mul]
      exact tendsto_const_nhds
    · have hxt : 0 < x j := lt_of_not_ge hx
      have he : (fun k => u x * kernelLaplacian (φ k) x) =ᶠ[atTop]
          (fun _ => u x * kernelLaplacian ψ x) := by
        filter_upwards [(tendsto_order.mp absRegularizationScale_tendsto).2 (x j / 2) (half_pos hxt)] with k hk
        have hkn : 2 * absRegularizationScale k < x j := by linarith
        have hneigh : φ k =ᶠ[𝓝 x] ψ := by
          filter_upwards [(isOpen_lt continuous_const
            (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous).mem_nhds hkn] with y hy
          change scaledFlatBoundaryStep (absRegularizationScale k) (y j) * ψ y = ψ y
          change 2 * absRegularizationScale k < y j at hy
          rw [scaledFlatBoundaryStep_one (absRegularizationScale_pos k) hy.le, one_mul]
        rw [kernelLaplacian_congr_nhds hneigh]
      exact tendsto_const_nhds.congr' he.symm
  have hconv := tendsto_integral_of_dominated_convergence bound
    (fun k => hu.aestronglyMeasurable.mul (continuous_kernelLaplacian (contDiff_infty.mp (hφ k) 2)).aestronglyMeasurable)
    hboundi hbound hlim
  have hzlim : Tendsto (fun k => ∫ x, u x * kernelLaplacian (φ k) x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hconv hzlim

end GaussianTilt.MomentMapLinearDirichlet
