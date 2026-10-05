import GaussianTilt.MomentMapEllipticFundamentalSolutionCutoff

/-!
# Genuine Hessian Green identity for C² functions

All fourth derivatives in this argument fall on the explicit smooth
regularized kernel. The test function needs only C² and compact support.
Two proved integrations by parts and the actual commutation of smooth
Fréchet derivatives identify its Hessian as a regularized singular integral.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def kernelDirectionalDerivative (v : KernelSpace n) (f : KernelSpace n → ℝ) : KernelSpace n → ℝ :=
  fun x => fderiv ℝ f x v

lemma smooth_kernelDirectionalDerivative {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : KernelSpace n) : ContDiff ℝ ∞ (kernelDirectionalDerivative v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma directionalHessian_eq_fderiv_fderiv {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (x v w : KernelSpace n) :
    directionalHessian f x v w = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl) x
  unfold directionalHessian
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

lemma kernelDirectionalDerivative_commute {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (v w : KernelSpace n) :
    kernelDirectionalDerivative v (kernelDirectionalDerivative w f) =
      kernelDirectionalDerivative w (kernelDirectionalDerivative v f) := by
  funext x
  change directionalHessian f x w v = directionalHessian f x v w
  rw [directionalHessian_eq_fderiv_fderiv hf, directionalHessian_eq_fderiv_fderiv hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) v w

lemma fourth_kernelDirectionalDerivative_exchange {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (a b i j : KernelSpace n) :
    kernelDirectionalDerivative b (kernelDirectionalDerivative a
      (kernelDirectionalDerivative j (kernelDirectionalDerivative i f))) =
      kernelDirectionalDerivative j (kernelDirectionalDerivative i
        (kernelDirectionalDerivative b (kernelDirectionalDerivative a f))) := by
  have hi := smooth_kernelDirectionalDerivative hf i
  have hai := smooth_kernelDirectionalDerivative hi a
  have ha := smooth_kernelDirectionalDerivative hf a
  rw [kernelDirectionalDerivative_commute (contDiff_infty.mp hi 2) a j,
    kernelDirectionalDerivative_commute (contDiff_infty.mp hai 2) b j,
    kernelDirectionalDerivative_commute (contDiff_infty.mp hf 2) a i,
    kernelDirectionalDerivative_commute (contDiff_infty.mp ha 2) b i]

lemma smooth_directionalHessian {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (v w : KernelSpace n) :
    ContDiff ℝ ∞ (fun x => directionalHessian f x v w) :=
  smooth_kernelDirectionalDerivative (smooth_kernelDirectionalDerivative hf v) w

lemma smooth_kernelLaplacian {f : KernelSpace n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (kernelLaplacian f) :=
  ContDiff.sum (fun _ _ => smooth_directionalHessian hf _ _)

lemma directionalHessian_sum {ι : Type*} [Fintype ι] (F : ι → KernelSpace n → ℝ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (x v w : KernelSpace n) :
    directionalHessian (fun y => ∑ i, F i y) x v w = ∑ i, directionalHessian (F i) x v w := by
  have he : (fun y => fderiv ℝ (fun z => ∑ i, F i z) y v) =
      (fun y => ∑ i, fderiv ℝ (F i) y v) := by
    funext y
    rw [fderiv_fun_sum (fun i _ => (hF i).differentiable (by norm_num) y)]
    simp only [ContinuousLinearMap.sum_apply]
  unfold directionalHessian
  rw [he, fderiv_fun_sum (fun i _ => (contDiff_directional_fderiv (hF i) v).differentiable le_rfl x)]
  simp only [ContinuousLinearMap.sum_apply]

lemma kernelLaplacian_directionalHessian_commute {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (x v w : KernelSpace n) :
    kernelLaplacian (fun y => directionalHessian f y v w) x =
      directionalHessian (kernelLaplacian f) x v w := by
  unfold kernelLaplacian
  rw [directionalHessian_sum _ (fun i => contDiff_infty.mp (smooth_directionalHessian hf _ _) 2)]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (fourth_kernelDirectionalDerivative_exchange hf _ _ v w) x

/-- Derivatives are exchanged using only C² test regularity; every fourth
derivative belongs to the smooth kernel. -/
theorem integral_kernelHessian_mul_laplacian_swap {u g : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) (hg : ContDiff ℝ ∞ g)
    (v w : KernelSpace n) :
    (∫ x, directionalHessian g x v w * kernelLaplacian u x) =
      ∫ x, directionalHessian u x w v * kernelLaplacian g x := by
  calc
    _ = ∫ x, kernelLaplacian u x * directionalHessian g x v w := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = ∫ x, u x * kernelLaplacian (fun y => directionalHessian g y v w) x :=
      (integral_mul_kernelLaplacian_swap hu (contDiff_infty.mp (smooth_directionalHessian hg v w) 2) hs).symm
    _ = ∫ x, u x * directionalHessian (kernelLaplacian g) x v w := by
      simp only [kernelLaplacian_directionalHessian_commute hg]
    _ = _ := integral_mul_directionalHessian_swap hu (contDiff_infty.mp (smooth_kernelLaplacian hg) 2) hs v w

/-- The true Hessian of a compactly supported C² function is the limit of
its regularized Newtonian Hessian integrals against its Laplacian. -/
theorem tendsto_regularized_hessian_green_pairing {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) (v w : KernelSpace n) :
    Tendsto (fun c : ℝ => ∫ x,
      directionalHessian (regularizedNewtonian n ((c ^ 2)⁻¹)) x v w * kernelLaplacian u x)
      atTop (𝓝 ((2 * (n : ℝ) * fundamentalApproxMass n) * directionalHessian u 0 w v)) := by
  let F : KernelSpace n → ℝ := fun x => directionalHessian u x w v
  have hFc : Continuous F := continuous_directionalHessian hu w v
  have hFs : HasCompactSupport F := (hs.fderiv_apply ℝ w).fderiv_apply ℝ v
  have happrox := fundamentalApproxDensity_approximate_identity (x₀ := 0)
    (hFc.integrable_of_hasCompactSupport hFs) hFc.continuousAt
  have heven (x : KernelSpace n) : fundamentalApproxDensity n (-x) = fundamentalApproxDensity n x := by
    simp only [fundamentalApproxDensity, fundamentalApproxBase, norm_neg]
  have hpeak : Tendsto (fun c : ℝ => ∫ x, (c ^ n * fundamentalApproxDensity n (c • x)) * F x)
      atTop (𝓝 (F 0)) := by
    simpa only [zero_sub, smul_neg, heven] using happrox
  have ht := hpeak.const_mul (2 * (n : ℝ) * fundamentalApproxMass n)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hg : ContDiff ℝ ∞ (regularizedNewtonian n ((c ^ 2)⁻¹)) := contDiff_regularizedNewtonian (by positivity)
  rw [integral_kernelHessian_mul_laplacian_swap hu hs hg v w]
  simp only [kernelLaplacian_regularized_eq_approxDensity hc]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp [F]; ring)

end GaussianTilt.MomentMapElliptic
