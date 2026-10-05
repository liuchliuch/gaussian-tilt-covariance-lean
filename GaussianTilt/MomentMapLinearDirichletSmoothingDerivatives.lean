import GaussianTilt.MomentMapLinearDirichletFlatWeakReflection
import GaussianTilt.MomentMapSchauderInterpolation

/-!
# Quantitative genuine derivatives of smooth compact kernel convolutions

Repeated actual convolution differentiation places all derivatives on the
constructed compact kernel. Its finite L¹ derivative norm bounds the true
third derivative and hence the Hessian Lipschitz modulus, uniformly in the
bounded input. This supplies harmonic Taylor constants independent of the
particular harmonic function.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff NNReal Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

section Vector
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def rightScalarMul (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    F →L[ℝ] ℝ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℝ).flip

def vectorKernelConvolution (K : KernelSpace n → F) (f : KernelSpace n → ℝ) : KernelSpace n → F :=
  convolution K f (rightScalarMul F) volume

lemma contDiff_vectorKernelConvolution {K : KernelSpace n → F} {f : KernelSpace n → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) (hf : LocallyIntegrable f volume) :
    ContDiff ℝ ∞ (vectorKernelConvolution K f) :=
  hKc.contDiff_convolution_left (rightScalarMul F) hK hf

lemma fderiv_vectorKernelConvolution {K : KernelSpace n → F} {f : KernelSpace n → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) (hf : LocallyIntegrable f volume)
    (x : KernelSpace n) :
    fderiv ℝ (vectorKernelConvolution K f) x = vectorKernelConvolution (fderiv ℝ K) f x := by
  have he : (rightScalarMul F).precompL (KernelSpace n) =
      rightScalarMul (KernelSpace n →L[ℝ] F) := by
    ext A c v
    rfl
  unfold vectorKernelConvolution
  rw [(hKc.hasFDerivAt_convolution_left (rightScalarMul F)
    (contDiff_infty.mp hK 1) hf x).fderiv, he]

lemma norm_vectorKernelConvolution_le {K : KernelSpace n → F} {f : KernelSpace n → ℝ}
    (hK : Continuous K) (hKc : HasCompactSupport K) {B : ℝ}
    (hfB : ∀ x, |f x| ≤ B) (x : KernelSpace n) :
    ‖vectorKernelConvolution K f x‖ ≤ B * ∫ y, ‖K y‖ := by
  have hKi : Integrable (fun y => ‖K y‖) (volume : Measure (KernelSpace n)) :=
    hK.norm.integrable_of_hasCompactSupport (hKc.comp_left norm_zero)
  have hb : ‖vectorKernelConvolution K f x‖ ≤ ∫ y, B * ‖K y‖ := by
    apply norm_integral_le_of_norm_le (hKi.const_mul B)
    apply ae_of_all
    intro y
    change ‖f (x-y) • K y‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hfB _) (norm_nonneg _)
  simpa only [integral_const_mul] using hb

/-- A fixed compact smooth kernel yields a uniform actual Hessian
Lipschitz bound for convolution against arbitrary bounded locally
integrable data. The constant is a true finite derivative integral. -/
theorem exists_vectorKernelConvolution_second_lipschitz {K : KernelSpace n → F}
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : KernelSpace n → ℝ, LocallyIntegrable f volume →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) → ∀ x y : KernelSpace n,
      ‖fderiv ℝ (fderiv ℝ (vectorKernelConvolution K f)) x -
        fderiv ℝ (fderiv ℝ (vectorKernelConvolution K f)) y‖ ≤ D * B * ‖x-y‖ := by
  let K₁ := fderiv ℝ K
  let K₂ := fderiv ℝ K₁
  let K₃ := fderiv ℝ K₂
  have hK₁ : ContDiff ℝ ∞ K₁ := hK.fderiv_right (m := ∞) (by simp)
  have hK₂ : ContDiff ℝ ∞ K₂ := hK₁.fderiv_right (m := ∞) (by simp)
  have hK₃ : ContDiff ℝ ∞ K₃ := hK₂.fderiv_right (m := ∞) (by simp)
  have hK₁c : HasCompactSupport K₁ := hKc.fderiv ℝ
  have hK₂c : HasCompactSupport K₂ := hK₁c.fderiv ℝ
  have hK₃c : HasCompactSupport K₃ := hK₂c.fderiv ℝ
  let D := ∫ y, ‖K₃ y‖
  have hD : 0 ≤ D := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨D, hD, ?_⟩
  intro f hf B hB hfB
  have he₁ : fderiv ℝ (vectorKernelConvolution K f) = vectorKernelConvolution K₁ f :=
    funext (fderiv_vectorKernelConvolution hK hKc hf)
  have he₂ : fderiv ℝ (fderiv ℝ (vectorKernelConvolution K f)) = vectorKernelConvolution K₂ f := by
    rw [he₁]
    exact funext (fderiv_vectorKernelConvolution hK₁ hK₁c hf)
  have he₃ (x : KernelSpace n) : fderiv ℝ (vectorKernelConvolution K₂ f) x = vectorKernelConvolution K₃ f x :=
    fderiv_vectorKernelConvolution hK₂ hK₂c hf x
  let L : ℝ≥0 := ⟨D*B, mul_nonneg hD hB⟩
  have hLip : LipschitzWith L (vectorKernelConvolution K₂ f) :=
    lipschitzWith_of_nnnorm_fderiv_le
      ((contDiff_vectorKernelConvolution hK₂ hK₂c hf).differentiable (by simp)) (by
        intro x
        change ‖fderiv ℝ (vectorKernelConvolution K₂ f) x‖ ≤ D*B
        rw [he₃]
        exact (norm_vectorKernelConvolution_le hK₃.continuous hK₃c hfB x).trans_eq (mul_comm B D))
  intro x y
  rw [he₂]
  exact hLip.norm_sub_le x y

end Vector

end GaussianTilt.MomentMapLinearDirichlet
