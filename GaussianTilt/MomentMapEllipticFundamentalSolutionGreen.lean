import GaussianTilt.MomentMapEllipticFundamentalSolutionRegularized

/-!
# Genuine regularized Green identity

Compact support supplies every integrability condition for two applications
of the proved whole-space Fréchet integration-by-parts theorem. The computed
regularized Laplacian is identified exactly with the normalized approximate
identity. Consequently the regularized Green pairing converges to evaluation.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The literal Euclidean Laplacian in its orthonormal coordinate frame. -/
def kernelLaplacian (f : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  ∑ i : Fin n, directionalHessian f x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ i)

lemma contDiff_directional_fderiv {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (v : KernelSpace n) :
    ContDiff ℝ 1 (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

lemma continuous_directionalHessian {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (v w : KernelSpace n) :
    Continuous (fun x => directionalHessian f x v w) :=
  ((contDiff_directional_fderiv hf v).continuous_fderiv le_rfl).clm_apply continuous_const

lemma integrable_compact_mul {f g : KernelSpace n → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) (hg : Continuous g) :
    Integrable (fun x => f x * g x) :=
  (hf.mul hg).integrable_of_hasCompactSupport hs.mul_right

/-- Two genuine integrations by parts exchange the actual second
Fréchet derivatives. Compactness eliminates all boundary terms. -/
theorem integral_mul_directionalHessian_swap {f g : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport f)
    (v w : KernelSpace n) :
    (∫ x, f x * directionalHessian g x v w) =
      ∫ x, directionalHessian f x w v * g x := by
  have hdf := contDiff_directional_fderiv hf w
  have hdg := contDiff_directional_fderiv hg v
  have hsdf := hs.fderiv_apply ℝ w
  have hsddf := hsdf.fderiv_apply ℝ v
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := w)
    (integrable_compact_mul hdf.continuous hsdf hdg.continuous)
    (integrable_compact_mul hf.continuous hs (continuous_directionalHessian hg v w))
    (integrable_compact_mul hf.continuous hs hdg.continuous)
    (hf.differentiable (by norm_num)) (hdg.differentiable le_rfl)
  have h2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := v)
    (integrable_compact_mul (continuous_directionalHessian hf w v) hsddf hg.continuous)
    (integrable_compact_mul hdf.continuous hsdf hdg.continuous)
    (integrable_compact_mul hdf.continuous hsdf hg.continuous)
    (hdf.differentiable le_rfl) (hg.differentiable (by norm_num))
  change (∫ x, f x * directionalHessian g x v w) =
    -(∫ x, fderiv ℝ f x w * fderiv ℝ g x v) at h1
  rw [h1, h2, neg_neg]
  rfl

/-- The actual second Green identity against a compactly supported C²
test function, with no boundary-decay premise. -/
theorem integral_mul_kernelLaplacian_swap {f g : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hs : HasCompactSupport f) :
    (∫ x, f x * kernelLaplacian g x) = ∫ x, kernelLaplacian f x * g x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hleft (i : Fin n) : Integrable (fun x => f x * directionalHessian g x (b i) (b i)) :=
    integrable_compact_mul hf.continuous hs (continuous_directionalHessian hg _ _)
  have hright (i : Fin n) : Integrable (fun x => directionalHessian f x (b i) (b i) * g x) :=
    integrable_compact_mul (continuous_directionalHessian hf _ _)
      ((hs.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b i)) hg.continuous
  simp only [kernelLaplacian, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finset_sum Finset.univ (fun i _ => hleft i),
    integral_finset_sum Finset.univ (fun i _ => hright i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_mul_directionalHessian_swap hf hg hs _ _

/-- Exact scaling identifies the computed regularized Laplacian with the
already normalized probability kernel. All dimensional factors are derived. -/
theorem kernelLaplacian_regularized_eq_approxDensity {c : ℝ} (hc : 0 < c)
    (x : KernelSpace n) :
    kernelLaplacian (regularizedNewtonian n ((c ^ 2)⁻¹)) x =
      (2 * (n : ℝ) * fundamentalApproxMass n) *
        (c ^ n * fundamentalApproxDensity n (c • x)) := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have ha : 0 < (c ^ 2)⁻¹ + ‖x‖ ^ 2 := by positivity
  have hnorm : 1 + ‖c • x‖ ^ 2 = c ^ 2 * ((c ^ 2)⁻¹ + ‖x‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    field_simp
  have hcpow : c ^ n = (c ^ 2) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast c n, ← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by ring]
  have hbase : c ^ n * fundamentalApproxBase n (c • x) =
      (c ^ 2)⁻¹ * ((c ^ 2)⁻¹ + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) := by
    rw [fundamentalApproxBase, hnorm, Real.mul_rpow hc2.le ha.le, hcpow]
    rw [← mul_assoc, ← Real.rpow_add hc2]
    rw [show (n : ℝ) / 2 + -((n : ℝ) + 2) / 2 = -1 by ring, Real.rpow_neg_one]
  rw [kernelLaplacian, trace_directionalHessian_regularizedNewtonian ha]
  change 2 * (n : ℝ) * (c ^ 2)⁻¹ * ((c ^ 2)⁻¹ + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) =
    (2 * (n : ℝ) * fundamentalApproxMass n) *
      (c ^ n * (fundamentalApproxBase n (c • x) / fundamentalApproxMass n))
  have hZ := (fundamentalApproxMass_pos n).ne'
  calc
    _ = 2 * (n : ℝ) * (c ^ n * fundamentalApproxBase n (c • x)) := by rw [hbase]; ring
    _ = _ := by field_simp

/-- The regularized Green pairing converges to point evaluation times the
explicit positive normalization. No distributional fundamental-solution
identity is presupposed: the limit is the proved approximation of identity. -/
theorem tendsto_regularized_green_pairing {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Tendsto (fun c : ℝ => ∫ x, regularizedNewtonian n ((c ^ 2)⁻¹) x * kernelLaplacian f x)
      atTop (𝓝 ((2 * (n : ℝ) * fundamentalApproxMass n) * f 0)) := by
  have happrox := fundamentalApproxDensity_approximate_identity (x₀ := 0)
    (hf.continuous.integrable_of_hasCompactSupport hs) hf.continuous.continuousAt
  have heven (x : KernelSpace n) : fundamentalApproxDensity n (-x) = fundamentalApproxDensity n x := by
    simp only [fundamentalApproxDensity, fundamentalApproxBase, norm_neg]
  have hpeak : Tendsto (fun c : ℝ => ∫ x, (c ^ n * fundamentalApproxDensity n (c • x)) * f x)
      atTop (𝓝 (f 0)) := by
    simpa only [zero_sub, smul_neg, heven] using happrox
  have ht := hpeak.const_mul (2 * (n : ℝ) * fundamentalApproxMass n)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hg : ContDiff ℝ 2 (regularizedNewtonian n ((c ^ 2)⁻¹)) :=
    contDiff_regularizedNewtonian (by positivity)
  have hibp := integral_mul_kernelLaplacian_swap hf hg hs
  rw [show (fun x => kernelLaplacian f x * regularizedNewtonian n ((c ^ 2)⁻¹) x) =
      (fun x => regularizedNewtonian n ((c ^ 2)⁻¹) x * kernelLaplacian f x) by funext x; ring] at hibp
  rw [← hibp]
  simp only [kernelLaplacian_regularized_eq_approxDensity hc]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

end GaussianTilt.MomentMapElliptic
