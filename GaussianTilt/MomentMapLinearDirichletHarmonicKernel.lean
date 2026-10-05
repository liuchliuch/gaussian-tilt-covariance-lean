import GaussianTilt.MomentMapEllipticFundamentalSolutionHessianGreen

/-!
# A genuine compact harmonic smoothing kernel

Cutting the singularity out of the proved Newtonian fundamental solution
produces a globally smooth potential whose Laplacian is compactly
supported. The actual Green identity proves that its normalized Laplacian
reproduces every locally harmonic compact C² function. No mean-value or
harmonic regularity theorem is assumed.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma contDiffAt_newtonianKernel {x : KernelSpace n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (newtonianKernel n) x := by
  have hh : ContDiffAt ℝ ∞ (fun y : KernelSpace n => ‖y‖ ^ 2) x :=
    (contDiff_id.norm_sq ℝ).contDiffAt
  have hnz : ‖x‖ ^ 2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
  change ContDiffAt ℝ ∞ (fun y : KernelSpace n => newtonianProfile n (0 + ‖y‖ ^ 2)) x
  simp only [zero_add]
  by_cases hn : n = 2
  · simp only [newtonianProfile, if_pos hn]
    exact hh.log hnz
  · simp only [newtonianProfile, if_neg hn]
    exact (hh.rpow_const_of_ne hnz).div_const _

lemma kernelLaplacian_newtonianKernel {x : KernelSpace n} (hx : x ≠ 0) :
    kernelLaplacian (newtonianKernel n) x = 0 := by
  simpa only [kernelLaplacian, newtonianKernel, mul_zero, zero_mul] using
    trace_directionalHessian_regularizedNewtonian (a := 0)
      (show 0 < (0 : ℝ) + ‖x‖ ^ 2 by simpa using sq_pos_of_pos (norm_pos_iff.mpr hx))

lemma kernelLaplacian_congr_nhds {f g : KernelSpace n → ℝ} {x : KernelSpace n}
    (h : f =ᶠ[𝓝 x] g) : kernelLaplacian f x = kernelLaplacian g x := by
  apply Finset.sum_congr rfl
  intro i _
  let e := EuclideanSpace.basisFun (Fin n) ℝ i
  have hi : (fun y => fderiv ℝ f y e) =ᶠ[𝓝 x] (fun y => fderiv ℝ g y e) :=
    h.fderiv.mono (fun y hy => congrArg (fun A : KernelSpace n →L[ℝ] ℝ => A e) hy)
  exact congrArg (fun A : KernelSpace n →L[ℝ] ℝ => A e) hi.fderiv_eq

/-- The singularity-removed genuine Newtonian potential. -/
def harmonicSmoothingPotential (χ : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  (1 - χ x) * newtonianKernel n x

def harmonicSmoothingKernel (χ : KernelSpace n → ℝ) : KernelSpace n → ℝ :=
  kernelLaplacian (harmonicSmoothingPotential χ)

lemma contDiff_harmonicSmoothingPotential {χ : KernelSpace n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1)) :
    ContDiff ℝ ∞ (harmonicSmoothingPotential χ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hχ0] with y hy
    simp [harmonicSmoothingPotential, hy]
  · exact (contDiffAt_const.sub hχ.contDiffAt).mul (contDiffAt_newtonianKernel hx)

lemma contDiff_harmonicSmoothingKernel {χ : KernelSpace n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1)) :
    ContDiff ℝ ∞ (harmonicSmoothingKernel χ) :=
  smooth_kernelLaplacian (contDiff_harmonicSmoothingPotential hχ hχ0)

lemma harmonicSmoothingKernel_support_subset {χ : KernelSpace n → ℝ}
    (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1)) :
    Function.support (harmonicSmoothingKernel χ) ⊆ tsupport χ := by
  intro x hx
  by_contra hxχ
  have hzero : χ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hxχ
  have hx0 : x ≠ 0 := by
    intro he
    subst x
    have h1 := hχ0.eq_of_nhds
    have h0 := hzero.eq_of_nhds
    norm_num at h1 h0
    linarith
  have he : harmonicSmoothingPotential χ =ᶠ[𝓝 x] newtonianKernel n := by
    filter_upwards [hzero] with y hy
    simp [harmonicSmoothingPotential, hy]
  exact hx ((kernelLaplacian_congr_nhds he).trans (kernelLaplacian_newtonianKernel hx0))

lemma hasCompactSupport_harmonicSmoothingKernel {χ : KernelSpace n → ℝ}
    (hχc : HasCompactSupport χ) (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1)) :
    HasCompactSupport (harmonicSmoothingKernel χ) :=
  HasCompactSupport.of_support_subset_isCompact hχc (harmonicSmoothingKernel_support_subset hχ0)

/-- The compact kernel genuinely reproduces locally harmonic compact C²
functions. Its normalization is the proved fundamental-solution mass. -/
theorem harmonicSmoothingKernel_reproduces [NeZero n]
    {χ h : KernelSpace n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1))
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h)
    (hharm : ∀ x ∈ tsupport χ, kernelLaplacian h x = 0) :
    (2 * (n : ℝ) * fundamentalApproxMass n) * h 0 =
      ∫ x, harmonicSmoothingKernel χ x * h x := by
  have hgreen := newtonian_green_identity hh hhc
  have hswap := integral_mul_kernelLaplacian_swap hh
    (contDiff_infty.mp (contDiff_harmonicSmoothingPotential hχ hχ0) 2) hhc
  have he : (∫ x, newtonianKernel n x * kernelLaplacian h x) =
      ∫ x, kernelLaplacian h x * harmonicSmoothingPotential χ x := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport χ
      · rw [hharm x hx, mul_zero, zero_mul]
      · rw [harmonicSmoothingPotential, image_eq_zero_of_notMem_tsupport hx]
        ring)
  rw [hgreen] at he
  calc
    _ = ∫ x, h x * kernelLaplacian (harmonicSmoothingPotential χ) x := he.trans hswap.symm
    _ = _ := by apply integral_congr_ae; exact ae_of_all _ (fun x => mul_comm _ _)

/-- The same exact smoothing identity at an arbitrary center. -/
theorem harmonicSmoothingKernel_reproduces_at [NeZero n]
    {χ h : KernelSpace n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : χ =ᶠ[𝓝 0] (fun _ => 1))
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) (x : KernelSpace n)
    (hharm : ∀ y ∈ tsupport χ, kernelLaplacian h (y + x) = 0) :
    (2 * (n : ℝ) * fundamentalApproxMass n) * h x =
      ∫ y, harmonicSmoothingKernel χ y * h (y + x) := by
  have hg := harmonicSmoothingKernel_reproduces hχ hχ0
    (hh.comp (contDiff_id.add contDiff_const)) (hasCompactSupport_kernel_translate hhc x)
    (by intro y hy; change kernelLaplacian (fun z => h (z + x)) y = 0; rw [kernelLaplacian_comp_add_right]; exact hharm y hy)
  simpa only [Function.comp_def, id_eq, zero_add] using hg

end GaussianTilt.MomentMapLinearDirichlet
