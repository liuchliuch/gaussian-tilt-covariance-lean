import GaussianTilt.MomentMapLinearDirichletHarmonicLimit

/-!
# Actual Euclidean mollifiers of a locally distribution-harmonic function

The canonical compact smooth probability kernels are constructed explicitly.
Their true Laplacians test the distributional equation, their sup bounds
follow from positivity and normalization, and their AE convergence follows
from the proved Lebesgue differentiation theorem.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def harmonicConvolution (ρ f : KernelSpace n → ℝ) : KernelSpace n → ℝ :=
  convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume

lemma harmonicConvolution_comm (ρ f : KernelSpace n → ℝ) :
    harmonicConvolution ρ f = harmonicConvolution f ρ := by
  have he : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by ext a b; simp [mul_comm]
  simpa only [harmonicConvolution, he] using
    (convolution_flip (ContinuousLinearMap.lsmul ℝ ℝ) (f := ρ) (g := f) (μ := volume)).symm

lemma harmonicConvolution_flip_apply (ρ f : KernelSpace n → ℝ) (x : KernelSpace n) :
    harmonicConvolution ρ f x = ∫ y, f y * ρ (x - y) := by
  rw [harmonicConvolution_comm]
  rfl

lemma kernelDirectionalDerivative_convolution {ρ f : KernelSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hf : LocallyIntegrable f volume)
    (v : KernelSpace n) :
    kernelDirectionalDerivative v (harmonicConvolution ρ f) =
      harmonicConvolution (kernelDirectionalDerivative v ρ) f := by
  rw [harmonicConvolution_comm ρ f]
  funext x
  unfold kernelDirectionalDerivative
  change (fderiv ℝ (convolution f ρ (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) v = _
  rw [(hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (contDiff_infty.mp hρ 1) x).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf (hρc.fderiv ℝ)
    ((contDiff_infty.mp hρ 1).continuous_fderiv le_rfl)]
  exact congrFun (harmonicConvolution_comm f (kernelDirectionalDerivative v ρ)) x

lemma kernelLaplacian_convolution {ρ f : KernelSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hf : LocallyIntegrable f volume)
    (x : KernelSpace n) :
    kernelLaplacian (harmonicConvolution ρ f) x = harmonicConvolution (kernelLaplacian ρ) f x := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hdir (i : Fin n) :
      (fun y => directionalHessian (harmonicConvolution ρ f) y (e i) (e i)) =
        harmonicConvolution (fun y => directionalHessian ρ y (e i) (e i)) f := by
    change kernelDirectionalDerivative (e i) (kernelDirectionalDerivative (e i) (harmonicConvolution ρ f)) = _
    rw [kernelDirectionalDerivative_convolution hρ hρc hf,
      kernelDirectionalDerivative_convolution (smooth_kernelDirectionalDerivative hρ _)
        (hρc.fderiv_apply ℝ _) hf]
    rfl
  have hi (i : Fin n) : Integrable (fun y => f y * directionalHessian ρ (x - y) (e i) (e i)) volume :=
    ((hρc.fderiv_apply ℝ (e i)).fderiv_apply ℝ (e i)).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hf (smooth_directionalHessian hρ _ _).continuous x
  change (∑ i, directionalHessian (harmonicConvolution ρ f) x (e i) (e i)) = _
  simp only [show ∀ i, directionalHessian (harmonicConvolution ρ f) x (e i) (e i) =
    harmonicConvolution (fun y => directionalHessian ρ y (e i) (e i)) f x from fun i => congrFun (hdir i) x,
    harmonicConvolution_flip_apply, kernelLaplacian, Finset.mul_sum]
  exact (integral_finset_sum _ (fun i _ => hi i)).symm

lemma kernelDirectionalDerivative_const_sub {ρ : KernelSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (a v x : KernelSpace n) :
    kernelDirectionalDerivative v (fun y => ρ (a - y)) x =
      -kernelDirectionalDerivative v ρ (a - x) := by
  unfold kernelDirectionalDerivative
  change (fderiv ℝ (ρ ∘ (fun y => a - y)) x) v = _
  rw [(((hρ.differentiable (by simp) (a - x)).hasFDerivAt).comp x
    ((hasFDerivAt_const a x).sub (hasFDerivAt_id x))).fderiv]
  simp

lemma kernelLaplacian_const_sub {ρ : KernelSpace n → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (a x : KernelSpace n) :
    kernelLaplacian (fun y => ρ (a - y)) x = kernelLaplacian ρ (a - x) := by
  apply Finset.sum_congr rfl
  intro i _
  let e := EuclideanSpace.basisFun (Fin n) ℝ i
  have hd : kernelDirectionalDerivative e (fun y => ρ (a - y)) =
      fun y => -kernelDirectionalDerivative e ρ (a - y) :=
    funext (kernelDirectionalDerivative_const_sub hρ a e)
  change kernelDirectionalDerivative e (kernelDirectionalDerivative e (fun y => ρ (a - y))) x = _
  rw [hd]
  change fderiv ℝ (fun y => -kernelDirectionalDerivative e ρ (a - y)) x e = _
  rw [fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]
  change -kernelDirectionalDerivative e (fun y => kernelDirectionalDerivative e ρ (a-y)) x = _
  rw [kernelDirectionalDerivative_const_sub (smooth_kernelDirectionalDerivative hρ e), neg_neg]
  rfl

lemma convolution_harmonic_of_distribution {Ω : Set (KernelSpace n)} {f ρ : KernelSpace n → ℝ}
    (hf : LocallyIntegrable f volume) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (heq : ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, f y * kernelLaplacian ψ y) = 0)
    (x : KernelSpace n) (hx : tsupport (fun y => ρ (x-y)) ⊆ Ω) :
    kernelLaplacian (harmonicConvolution ρ f) x = 0 := by
  have hψ : ContDiff ℝ ∞ (fun y => ρ (x-y)) := hρ.comp (contDiff_const.sub contDiff_id)
  have he := heq _ hψ (hρc.comp_homeomorph (Homeomorph.subLeft x)) hx
  simp only [kernelLaplacian_const_sub hρ] at he
  rw [kernelLaplacian_convolution hρ hρc hf, harmonicConvolution_flip_apply]
  exact he

def harmonicMollifierBump (n k : ℕ) : ContDiffBump (0 : KernelSpace n) :=
  ⟨(((k : ℝ) + 1)⁻¹) / 2, ((k : ℝ) + 1)⁻¹, by positivity, half_lt_self (by positivity)⟩

def harmonicMollify (k : ℕ) (f : KernelSpace n → ℝ) : KernelSpace n → ℝ :=
  harmonicConvolution ((harmonicMollifierBump n k).normed volume) f

lemma harmonicMollify_smooth {f : KernelSpace n → ℝ} (hf : LocallyIntegrable f volume) (k : ℕ) :
    ContDiff ℝ ∞ (harmonicMollify k f) :=
  (harmonicMollifierBump n k).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (harmonicMollifierBump n k).contDiff_normed hf

lemma harmonicMollify_compact {f : KernelSpace n → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (harmonicMollify k f) :=
  (harmonicMollifierBump n k).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf

lemma harmonicMollify_bound {f : KernelSpace n → ℝ} {B : ℝ}
    (hf : ∀ y, |f y| ≤ B) (k : ℕ) (x : KernelSpace n) : |harmonicMollify k f x| ≤ B := by
  have hi := (harmonicMollifierBump n k).integrable_normed (μ := (volume : Measure (KernelSpace n)))
  have hnorm : ‖harmonicMollify k f x‖ ≤ ∫ y, (harmonicMollifierBump n k).normed volume y * B := by
    apply norm_integral_le_of_norm_le (hi.mul_const B)
    apply ae_of_all
    intro y
    change ‖(harmonicMollifierBump n k).normed volume y * f (x-y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((harmonicMollifierBump n k).nonneg_normed y)]
    exact mul_le_mul_of_nonneg_left (hf (x-y)) ((harmonicMollifierBump n k).nonneg_normed y)
  simpa only [Real.norm_eq_abs, integral_mul_const, ContDiffBump.integral_normed, one_mul] using hnorm

lemma harmonicMollify_ae_tendsto {f : KernelSpace n → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (fun k => harmonicMollify k f x) atTop (𝓝 (f x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := harmonicMollifierBump n) (K := 2)
  · change Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0)
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  · exact Eventually.of_forall (fun k => by
      change ((k : ℝ) + 1)⁻¹ ≤ 2 * (((k : ℝ) + 1)⁻¹ / 2)
      linarith)
  · exact hf

end GaussianTilt.MomentMapLinearDirichlet
