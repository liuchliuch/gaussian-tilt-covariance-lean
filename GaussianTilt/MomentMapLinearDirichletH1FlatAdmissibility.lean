import GaussianTilt.MomentMapLinearDirichletH1FlatTestBounds

/-! # Odd smooth tests are genuinely admissible for the H¹ weak equation

A first-order boundary cutoff has uniformly bounded gradient because the
smooth test vanishes on the plane. Dominated convergence uses only local
integrability of the actual weak gradient and its zero extension.
-/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem integral_gradient_flat_zero_test (j : Fin n)
    {G : Fin n → KernelSpace n → ℝ} (hG : ∀ i, LocallyIntegrable (G i) volume)
    (hG0 : ∀ i, ∀ᵐ x ∂volume, x j ≤ 0 → G i x=0) {R : ℝ}
    (heq : ∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R ∩ {x | 0 < x j} →
      (∑ i, ∫ x, G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) φ x)=0)
    {ψ : KernelSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψR : tsupport ψ ⊆ Metric.ball 0 R) (hψ0 : ∀ x, x j=0 → ψ x=0) :
    (∑ i, ∫ x, G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x)=0 := by
  obtain ⟨D,hD,hψheight,hψgrad⟩ := exists_flat_test_first_bounds j hψ hψc hψ0
  obtain ⟨M,M₂,hM,hM₂,hstep,_⟩ := exists_flatBoundaryStep_derivative_bounds
  let φ := fun k x => scaledFlatBoundaryStep (absRegularizationScale k) (x j)*ψ x
  have hφ (k : ℕ) : ContDiff ℝ ∞ (φ k) :=
    (contDiff_coordinate_profile (scaledFlatBoundaryStep_contDiff _) j).mul hψ
  have hφc (k : ℕ) : HasCompactSupport (φ k) := hψc.mul_left
  have hφs (k : ℕ) : tsupport (φ k) ⊆ tsupport ψ := tsupport_scaledFlatBoundaryStep_mul j
  have hφΩ (k : ℕ) : tsupport (φ k) ⊆ Metric.ball 0 R ∩ {x | 0 < x j} :=
    subset_inter ((hφs k).trans hψR)
      (tsupport_scaledFlatBoundaryStep_mul_positive (absRegularizationScale_pos k) ψ j)
  let C := D+2*M*D
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hconv (i : Fin n) : Tendsto
      (fun k : ℕ => ∫ x, G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (φ k) x)
      atTop (𝓝 (∫ x, G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x)) := by
    let bound := (tsupport ψ).indicator (fun x => |G i x| *C)
    have hbint : Integrable bound volume := by
      apply IntegrableOn.integrable_indicator _ hψc.measurableSet
      exact ((hG i).integrableOn_isCompact hψc).norm.mul_const C
    have hb (k : ℕ) : ∀ᵐ x ∂volume,
        ‖G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (φ k) x‖ ≤ bound x := by
      apply ae_of_all
      intro x
      by_cases hx : x ∈ tsupport ψ
      · rw [show bound x=|G i x| *C from indicator_of_mem hx _,Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_left
          (scaledFlatBoundaryStep_test_first_bound j i hψ (absRegularizationScale_pos k) hD hM hψheight hψgrad hstep x)
          (abs_nonneg _)
      · rw [show bound x=0 from indicator_of_notMem hx _,
          kernelDerivative_zero_off_tsupport (φ k) _ (fun hh => hx (hφs k hh)),mul_zero,norm_zero]
    have hlim : ∀ᵐ x ∂volume, Tendsto
        (fun k => G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (φ k) x)
        atTop (𝓝 (G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x)) := by
      filter_upwards [hG0 i] with x hxzero
      by_cases hx : x j ≤ 0
      · simp only [hxzero hx,zero_mul]
        exact tendsto_const_nhds
      · have hxt : 0 < x j := lt_of_not_ge hx
        have he : (fun k => G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (φ k) x) =ᶠ[atTop]
            (fun _ => G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x) := by
          filter_upwards [(tendsto_order.mp absRegularizationScale_tendsto).2 (x j/2) (half_pos hxt)] with k hk
          have hkn : 2*absRegularizationScale k < x j := by linarith
          have hneigh : φ k =ᶠ[𝓝 x] ψ := by
            filter_upwards [(isOpen_lt continuous_const
              (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous).mem_nhds hkn] with y hy
            change 2*absRegularizationScale k < y j at hy
            change scaledFlatBoundaryStep (absRegularizationScale k) (y j)*ψ y=ψ y
            rw [scaledFlatBoundaryStep_one (absRegularizationScale_pos k) hy.le,one_mul]
          rw [kernelDerivative_congr_nhds hneigh]
        exact tendsto_const_nhds.congr' he.symm
    apply tendsto_integral_of_dominated_convergence bound _ hbint hb hlim
    intro k
    exact (hG i).aestronglyMeasurable.mul
      (((hφ k).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.aestronglyMeasurable
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => hconv i)
  have he (k : ℕ) : (∑ i, ∫ x, G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (φ k) x)=0 :=
    heq _ (hφ k) (hφc k) (hφΩ k)
  have hz : Tendsto (fun k : ℕ => ∑ i, ∫ x, G i x*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (φ k) x)
      atTop (𝓝 (0:ℝ)) := by simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hsum hz

end GaussianTilt.MomentMapLinearDirichlet
