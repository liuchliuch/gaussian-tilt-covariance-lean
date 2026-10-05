import GaussianTilt.MomentMapLinearDirichletFlatResidual

/-! # Actual weak polynomial subtraction with its corrected forcing -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Compact upper-half-space subtraction of a smooth plane-zero function.
The forcing correction follows from actual Green integration by parts. -/
theorem FlatWeakPoisson.subtractSmooth {j : Fin n} {u f P g : KernelSpace n → ℝ}
    (h : FlatWeakPoisson j u f) (hf : Continuous f) (hg : Continuous g)
    (hP : ContDiff ℝ ∞ P) (hP0 : ∀ x, x j = 0 → P x = 0)
    (hsource : ∀ x ∈ flatUpperBall j 2, g x = f x + kernelLaplacian P x) :
    FlatWeakPoisson j (flatResidual j u P) g := by
  have hpLp := flatPolynomialCutoff_memLp j hP.continuous
  refine ⟨h.memLp.sub hpLp, ?_, h.continuous.sub (flatPolynomialCutoff_continuousOn j hP.continuous), ?_, ?_⟩
  · intro x hx
    simp only [flatResidual, h.zero_lower x hx, flatPolynomialCutoff_zero_lower j P hx, sub_self]
  · obtain ⟨C, hC, hg⟩ := h.growth
    have hψ : ContDiff ℝ ∞ (fun x => flatResidualBump n x * P x) := (flatResidualBump n).contDiff.mul hP
    have hψc : HasCompactSupport (fun x => flatResidualBump n x * P x) := (flatResidualBump n).hasCompactSupport.mul_right
    obtain ⟨D, M, hD, _, hψg, _, _⟩ := exists_flat_test_bounds j hψ hψc (fun x hx => by rw [hP0 x hx, mul_zero])
    refine ⟨C+D, add_nonneg hC hD, ?_⟩
    intro x hx
    have hcut : |flatPolynomialCutoff j P x| ≤ D*|x j| := by
      by_cases hj : 0 < x j
      · rw [flatPolynomialCutoff, indicator_of_mem (show x ∈ {y : KernelSpace n | 0 < y j} from hj)]
        exact hψg x
      · rw [flatPolynomialCutoff, indicator_of_notMem (show x ∉ {y : KernelSpace n | 0 < y j} from hj), abs_zero]
        positivity
    exact (abs_sub _ _).trans ((add_le_add (hg x hx) hcut).trans_eq (by ring))
  · intro ψ hψ hψc hψs
    have huI := integrable_locally_mul_laplacian (h.memLp.locallyIntegrable (by norm_num)) (contDiff_infty.mp hψ 2) hψc
    have hpI := integrable_locally_mul_laplacian (hpLp.locallyIntegrable (by norm_num)) (contDiff_infty.mp hψ 2) hψc
    have hfI : Integrable (fun x => f x*ψ x) := (hf.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
    have hlc : Continuous (kernelLaplacian P) := continuous_kernelLaplacian (contDiff_infty.mp hP 2)
    have hlI : Integrable (fun x => kernelLaplacian P x*ψ x) :=
      (hlc.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
    have hpcut : (∫ x, flatPolynomialCutoff j P x * kernelLaplacian ψ x) =
        ∫ x, kernelLaplacian P x*ψ x := by
      calc
        _ = ∫ x, P x * kernelLaplacian ψ x := by
          apply integral_congr_ae
          exact ae_of_all _ (fun x => by
            dsimp only
            by_cases hx : x ∈ tsupport ψ
            · rw [flatPolynomialCutoff_eq j P (hψs hx)]
            · rw [kernelLaplacian_zero_off_tsupport ψ hx, mul_zero, mul_zero])
        _ = ∫ x, ψ x * kernelLaplacian P x := by
          have hh := integral_mul_kernelLaplacian_swap (contDiff_infty.mp hψ 2) (contDiff_infty.mp hP 2) hψc
          rw [hh]
          apply integral_congr_ae; exact ae_of_all _ (fun x => mul_comm _ _)
        _ = _ := by apply integral_congr_ae; exact ae_of_all _ (fun x => mul_comm _ _)
    have hgint : (∫ x, g x*ψ x) = (∫ x, f x*ψ x)+(∫ x, kernelLaplacian P x*ψ x) := by
      rw [← integral_add hfI hlI]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        dsimp only
        by_cases hx : x ∈ tsupport ψ
        · rw [hsource x (hψs hx), add_mul]
        · rw [image_eq_zero_of_notMem_tsupport hx]; simp)
    simp only [flatResidual, sub_mul]
    rw [integral_sub huI hpI, hpcut, h.equation ψ hψ hψc hψs, hgint]
    ring

end GaussianTilt.MomentMapLinearDirichlet
