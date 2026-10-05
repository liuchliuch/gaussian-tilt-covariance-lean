import GaussianTilt.MomentMapEllipticFundamentalSolutionHessianRepresentation
import GaussianTilt.MomentMapHolderDerivativeLimit

/-! # The actual Newtonian potential of smooth compact data -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- Unnormalized literal Newtonian convolution. Its Laplacian has the
positive normalization constructed in the fundamental-solution theorem. -/
def newtonianPotential (f : KernelSpace n → ℝ) : KernelSpace n → ℝ :=
  newtonianKernel n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f

lemma newtonianPotential_eq_integral (f : KernelSpace n → ℝ) (x : KernelSpace n) :
    newtonianPotential f x = ∫ y, newtonianKernel n (x - y) * f y := by
  have he := (volume.measurePreserving_sub_left x).integral_comp
    (Homeomorph.subLeft x).measurableEmbedding (fun y => newtonianKernel n y * f (x - y))
  simpa only [newtonianPotential, convolution_def, ContinuousLinearMap.mul_apply', sub_sub_cancel] using he.symm

lemma newtonianPotential_eq_add_integral (f : KernelSpace n → ℝ) (x : KernelSpace n) :
    newtonianPotential f x = ∫ y, newtonianKernel n y * f (y + x) := by
  have he := integral_neg_eq_self (μ := volume) (fun y => newtonianKernel n y * f (x - y))
  simpa only [newtonianPotential, convolution_def, ContinuousLinearMap.mul_apply',
    newtonianKernel_neg, sub_neg_eq_add, add_comm x] using he.symm

lemma smooth_newtonianPotential {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) : ContDiff ℝ ∞ (newtonianPotential f) :=
  hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel n) hf

lemma newtonianPotential_directional_derivative {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (x v : KernelSpace n) :
    fderiv ℝ (newtonianPotential f) x v = newtonianPotential (kernelDirectionalDerivative v f) x := by
  unfold newtonianPotential
  rw [(hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel n) (contDiff_infty.mp hf 1) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_newtonianKernel n) (hs.fderiv ℝ) (hf.continuous_fderiv (by simp)) x v

lemma newtonianPotential_directional_hessian {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (x v w : KernelSpace n) :
    directionalHessian (newtonianPotential f) x v w =
      newtonianPotential (fun y => directionalHessian f y v w) x := by
  have he : (fun y => fderiv ℝ (newtonianPotential f) y v) =
      newtonianPotential (kernelDirectionalDerivative v f) := funext (fun y => newtonianPotential_directional_derivative hf hs y v)
  unfold directionalHessian
  rw [he, newtonianPotential_directional_derivative (smooth_kernelDirectionalDerivative hf v)
    (hs.fderiv_apply ℝ v)]
  rfl

lemma newtonianPotential_laplacian_commute {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (x : KernelSpace n) :
    kernelLaplacian (newtonianPotential f) x = newtonianPotential (kernelLaplacian f) x := by
  unfold kernelLaplacian
  simp only [newtonianPotential_directional_hessian hf hs]
  simp only [newtonianPotential, convolution_def, ContinuousLinearMap.mul_apply', Finset.mul_sum]
  rw [integral_finset_sum]
  intro i _
  exact ((hs.fderiv_apply ℝ _).fderiv_apply ℝ _).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_newtonianKernel n)
      (smooth_directionalHessian hf _ _).continuous x

/-- The actual Poisson equation follows from the proved distributional
normalization and convolution differentiation. -/
theorem newtonianPotential_laplacian [NeZero n] {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (x : KernelSpace n) :
    kernelLaplacian (newtonianPotential f) x = (2 * (n : ℝ) * fundamentalApproxMass n) * f x := by
  rw [newtonianPotential_laplacian_commute hf hs, newtonianPotential_eq_add_integral]
  have htrans : ContDiff ℝ 2 (fun y => f (y + x)) :=
    (contDiff_infty.mp hf 2).comp (contDiff_id.add contDiff_const)
  have he := newtonian_green_identity htrans (hasCompactSupport_kernel_translate hs x)
  simpa only [kernelLaplacian_comp_add_right, zero_add] using he

end GaussianTilt.MomentMapLinearDirichlet
