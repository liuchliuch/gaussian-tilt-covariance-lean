import GaussianTilt.MomentMapLinearDirichletHarmonicL2Local
import GaussianTilt.MomentMapLinearDirichletSmoothingDerivatives

/-! # Genuine L² bounds for actual compact-kernel derivatives -/
noncomputable section
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal NNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Actual Hilbert Cauchy--Schwarz bounds vector-kernel convolution by the
L² input norm. The kernel constant is constructed from its own L² norm. -/
theorem exists_vectorKernelConvolution_L2_bound {K : KernelSpace n → F}
    (hK : Continuous K) (hKc : HasCompactSupport K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : KernelSpace n → ℝ, ∀ hf : MemLp f 2 volume,
      ∀ x, ‖vectorKernelConvolution K f x‖ ≤ D*‖hf.toLp f‖ := by
  have hKn : MemLp (fun y => ‖K y‖) 2 volume := hK.norm.memLp_of_hasCompactSupport (hKc.comp_left norm_zero)
  let D := ‖hKn.toLp (fun y => ‖K y‖)‖
  refine ⟨D,norm_nonneg _,?_⟩
  intro f hf x
  have hμ : MeasurePreserving (fun y : KernelSpace n => x-y) volume volume :=
    Measure.measurePreserving_sub_left volume x
  have hfn : MemLp (fun y => ‖f (x-y)‖) 2 volume := hf.norm.comp_measurePreserving hμ
  have hfn_norm : ‖hfn.toLp (fun y => ‖f (x-y)‖)‖=‖hf.toLp f‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_toLp_sq_eq_integral hfn,norm_toLp_sq_eq_integral hf]
    simp only [Real.norm_eq_abs,sq_abs]
    exact integral_sub_left_eq_self (fun y => f y^2) volume x
  calc
    ‖vectorKernelConvolution K f x‖ ≤ ∫ y, ‖f (x-y) • K y‖ := norm_integral_le_integral_norm _
    _ = ∫ y, ‖K y‖*‖f (x-y)‖ := by simp_rw [norm_smul,mul_comm]
    _ = inner ℝ (hKn.toLp (fun y => ‖K y‖)) (hfn.toLp (fun y => ‖f (x-y)‖)) :=
      (inner_toLp_eq_integral_mul hKn hfn).symm
    _ ≤ ‖inner ℝ (hKn.toLp (fun y => ‖K y‖)) (hfn.toLp (fun y => ‖f (x-y)‖))‖ := le_abs_self _
    _ ≤ D*‖hfn.toLp (fun y => ‖f (x-y)‖)‖ := norm_inner_le_norm _ _
    _ = D*‖hf.toLp f‖ := by rw [hfn_norm]

/-- Actual convolution differentiation gives a dimension/kernel-only
Lipschitz constant proportional to the L² norm of the data. -/
theorem exists_vectorKernelConvolution_L2_lipschitz {K : KernelSpace n → F}
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : KernelSpace n → ℝ, ∀ hf : MemLp f 2 volume,
      ∀ x y, ‖vectorKernelConvolution K f x-vectorKernelConvolution K f y‖ ≤
        D*‖hf.toLp f‖*‖x-y‖ := by
  obtain ⟨D,hD,hb⟩ := exists_vectorKernelConvolution_L2_bound
    (hK.fderiv_right (m := ∞) (by simp)).continuous (hKc.fderiv ℝ)
  refine ⟨D,hD,?_⟩
  intro f hf x y
  let L : ℝ≥0 := ⟨D*‖hf.toLp f‖,mul_nonneg hD (norm_nonneg _)⟩
  have hLip : LipschitzWith L (vectorKernelConvolution K f) :=
    lipschitzWith_of_nnnorm_fderiv_le
      ((contDiff_vectorKernelConvolution hK hKc (hf.locallyIntegrable (by norm_num))).differentiable (by simp)) (by
        intro z
        change ‖fderiv ℝ (vectorKernelConvolution K f) z‖ ≤ D*‖hf.toLp f‖
        rw [fderiv_vectorKernelConvolution hK hKc (hf.locallyIntegrable (by norm_num))]
        exact hb f hf z)
  exact hLip.norm_sub_le x y

end GaussianTilt.MomentMapLinearDirichlet
