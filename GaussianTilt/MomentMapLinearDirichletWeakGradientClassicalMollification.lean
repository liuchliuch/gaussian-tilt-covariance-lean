import GaussianTilt.MomentMapLinearDirichletHarmonicRegularity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Actual mollification of a continuous distributional gradient -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The genuine normalized convolution, also for vector and covector fields. -/
def weakGradientMollify {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : KernelSpace n → F) : KernelSpace n → F :=
  convolution ((harmonicMollifierBump n k).normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume

lemma harmonicMollifier_radius_tendsto :
    Tendsto (fun k : ℕ => (harmonicMollifierBump n k).rOut) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- Local uniform convergence is obtained from the actual joint-variable
approximate-identity theorem, not from a pointwise convergence shortcut. -/
theorem weakGradientMollify_tendstoLocallyUniformly
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : KernelSpace n → F} (hf : Continuous f) :
    TendstoLocallyUniformly (fun k => weakGradientMollify k f) f atTop := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro x
  have hconv : Tendsto (fun p : ℕ × KernelSpace n => weakGradientMollify p.1 f p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (f x)) := by
    apply ContDiffBump.convolution_tendsto_right
      (φ := fun p : ℕ × KernelSpace n => harmonicMollifierBump n p.1)
      (g := fun _ : ℕ × KernelSpace n => f)
    · exact harmonicMollifier_radius_tendsto.comp tendsto_fst
    · exact Eventually.of_forall (fun _ => hf.aestronglyMeasurable)
    · exact (hf.tendsto x).comp tendsto_snd
    · exact tendsto_snd
  exact (((hf.tendsto x).comp tendsto_snd).prodMk_nhds hconv).mono_right (nhds_le_uniformity (f x))

lemma weakGradientMollify_apply
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ} (hD : Continuous D)
    (k : ℕ) (x v : KernelSpace n) :
    weakGradientMollify k D x v = harmonicMollify k (fun y => D y v) x := by
  have hi : Integrable (fun y => (harmonicMollifierBump n k).normed volume y • D (x-y)) volume :=
    (harmonicMollifierBump n k).hasCompactSupport_normed.convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (harmonicMollifierBump n k).continuous_normed hD.locallyIntegrable x
  unfold weakGradientMollify harmonicMollify harmonicConvolution
  simp only [convolution_def,ContinuousLinearMap.lsmul_apply]
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

lemma convolution_directionalDerivative_of_weak_gradient
    {Ω : Set (KernelSpace n)} {u ρ : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    (hu : LocallyIntegrable u volume) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y))
    (x : KernelSpace n) (hx : tsupport (fun y => ρ (x-y)) ⊆ Ω) (i : Fin n) :
    kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (harmonicConvolution ρ u) x =
      harmonicConvolution ρ (fun y => D y (EuclideanSpace.basisFun (Fin n) ℝ i)) x := by
  have hψ : ContDiff ℝ ∞ (fun y => ρ (x-y)) := hρ.comp (contDiff_const.sub contDiff_id)
  have he := hweak i _ hψ (hρc.comp_homeomorph (Homeomorph.subLeft x)) hx
  simp only [kernelDirectionalDerivative_const_sub hρ,mul_neg,integral_neg] at he
  rw [kernelDirectionalDerivative_convolution hρ hρc hu,harmonicConvolution_flip_apply,harmonicConvolution_flip_apply]
  exact neg_injective he

/-- The true Fréchet derivative of the mollified function is the mollified
weak covector, whenever the translated test kernel stays in the domain. -/
theorem harmonicMollify_hasFDerivAt_of_weak_gradient
    {Ω : Set (KernelSpace n)} {u : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    (hu : Continuous u) (hD : Continuous D)
    (hweak : ∀ i : Fin n, ∀ ψ : KernelSpace n → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ y, u y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y) =
        -(∫ y, D y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y))
    (k : ℕ) (x : KernelSpace n)
    (hx : tsupport (fun y => (harmonicMollifierBump n k).normed volume (x-y)) ⊆ Ω) :
    HasFDerivAt (harmonicMollify k u) (weakGradientMollify k D x) x := by
  have hdiff := (harmonicMollify_smooth hu.locallyIntegrable k).differentiable (by simp) x
  convert hdiff.hasFDerivAt using 1
  apply ContinuousLinearMap.ext
  intro v
  have hL : (weakGradientMollify k D x).toLinearMap = (fderiv ℝ (harmonicMollify k u) x).toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
    intro i
    change weakGradientMollify k D x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (harmonicMollify k u) x
    rw [weakGradientMollify_apply hD]
    exact (convolution_directionalDerivative_of_weak_gradient hu.locallyIntegrable
      (harmonicMollifierBump n k).contDiff_normed (harmonicMollifierBump n k).hasCompactSupport_normed
      hweak x hx i).symm
  exact LinearMap.congr_fun hL v

end GaussianTilt.MomentMapLinearDirichlet
