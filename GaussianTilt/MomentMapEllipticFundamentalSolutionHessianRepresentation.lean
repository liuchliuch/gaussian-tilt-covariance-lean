import GaussianTilt.MomentMapEllipticFundamentalSolutionHessianMass

/-!
# Actual Hessian singular-integral representation

The regularized Hessian Green identity is decomposed into the compensated
local kernel, its concentrated diagonal mass, and the nonsingular tail.
Every limit and local correction has already been proved. Only C² regularity
of the compact test function is needed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapElliptic
open GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma newtonianHessianEntry_neg (i j : Fin n) (x : KernelSpace n) :
    newtonianHessianEntry i j (-x) = newtonianHessianEntry i j x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [newtonianHessianEntry_formula (neg_ne_zero.mpr hx), newtonianHessianEntry_formula hx]
    simp only [norm_neg, PiLp.neg_apply]
    ring

lemma cutoffNewtonianHessian_neg (χ : ℝ → ℝ) (i j : Fin n) (x : KernelSpace n) :
    cutoffNewtonianHessian χ i j (-x) = cutoffNewtonianHessian χ i j x := by
  simp only [cutoffNewtonianHessian, norm_neg, newtonianHessianEntry_neg]

lemma standardNewtonianTail_neg (i j : Fin n) (x : KernelSpace n) :
    standardNewtonianTail i j (-x) = standardNewtonianTail i j x :=
  cutoffNewtonianHessian_neg _ i j x

lemma regularized_hessian_integral_decomposition {f : KernelSpace n → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    (∫ x, regularizedHessianEntry a i j x * f x) =
      (∫ x, weightedRegularizedHessian a i j x * (f x - f 0)) +
        (∫ x, weightedRegularizedHessian a i j x) * f 0 +
        ∫ x, (1 - standardRadialCutoff ‖x‖) * regularizedHessianEntry a i j x * f x := by
  have hKc := continuous_regularizedHessianEntry ha i j
  have hχc : Continuous (fun x : KernelSpace n => standardRadialCutoff ‖x‖) :=
    standardRadialCutoff_contDiff.continuous.comp continuous_norm
  have hWc : Continuous (weightedRegularizedHessian a i j) := hχc.mul hKc
  have hWs : HasCompactSupport (weightedRegularizedHessian a i j) :=
    (standardRadialCutoff_norm_compact n).mul_right
  have hcore : Integrable (fun x => weightedRegularizedHessian a i j x * (f x - f 0)) :=
    integrable_compact_mul hWc hWs (hf.sub continuous_const)
  have hmass : Integrable (fun x => weightedRegularizedHessian a i j x * f 0) :=
    (integrable_weightedRegularizedHessian ha i j).mul_const _
  have htail : Integrable (fun x => (1 - standardRadialCutoff ‖x‖) * regularizedHessianEntry a i j x * f x) :=
    (((continuous_const.sub hχc).mul hKc).mul hf).integrable_of_hasCompactSupport hs.mul_left
  have he : (fun x => regularizedHessianEntry a i j x * f x) =
      (fun x => weightedRegularizedHessian a i j x * (f x - f 0) +
        weightedRegularizedHessian a i j x * f 0 +
        (1 - standardRadialCutoff ‖x‖) * regularizedHessianEntry a i j x * f x) := by
    funext x
    dsimp [weightedRegularizedHessian]
    ring
  have hsplit := integral_add (hcore.add hmass) htail
  simp only [Pi.add_apply] at hsplit
  rw [he, hsplit, integral_add hcore hmass, integral_mul_const]

/-- The full regularized Hessian integral has its actual local and tail
limit for Hölder source data. -/
theorem tendsto_regularized_hessian_integral [NeZero n]
    {f : KernelSpace n → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hαn : α < (n : ℝ))
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (i j : Fin n) :
    Tendsto (fun c : ℝ => ∫ x, regularizedHessianEntry ((c ^ 2)⁻¹) i j x * f x) atTop
      (𝓝 (standardNewtonianSingularIntegral f i j 0 +
        (if i = j then 2 * fundamentalApproxMass n else 0) * f 0 +
        scalarKernelConvolution volume (standardNewtonianTail i j) f 0)) := by
  have hc := tendsto_regularized_compensated_hessian hf.measurable hH hα hαn hholder i j
  have hm := (tendsto_weightedRegularizedHessian_mass i j).mul_const (f 0)
  have ht := tendsto_regularized_hessian_tail hf hs i j
  have hsum := (hc.add hm).add ht
  have hecore : (∫ x, cutoffNewtonianHessian standardRadialCutoff i j x * (f x - f 0)) =
      standardNewtonianSingularIntegral f i j 0 := by
    simp only [standardNewtonianSingularIntegral, compensatedSingularIntegral, zero_sub,
      cutoffNewtonianHessian_neg]
  have hetail : (∫ x, standardNewtonianTail i j x * f x) =
      scalarKernelConvolution volume (standardNewtonianTail i j) f 0 := by
    simp only [scalarKernelConvolution, zero_sub, standardNewtonianTail_neg]
  rw [hecore, hetail] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  exact (regularized_hessian_integral_decomposition hf hs (by positivity) i j).symm

/-- The genuine Hessian formula at the origin, including the derived local
Kronecker correction. The potential itself is only assumed C². -/
theorem compact_hessian_green_identity_zero [NeZero n] {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hf : ∀ x y, |kernelLaplacian u x - kernelLaplacian u y| ≤ H * ‖x - y‖ ^ α)
    (i j : Fin n) :
    (2 * (n : ℝ) * fundamentalApproxMass n) *
        directionalHessian u 0 (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) =
      standardNewtonianSingularIntegral (kernelLaplacian u) i j 0 +
        (if i = j then 2 * fundamentalApproxMass n else 0) * kernelLaplacian u 0 +
        scalarKernelConvolution volume (standardNewtonianTail i j) (kernelLaplacian u) 0 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hsym : directionalHessian u 0 (b j) (b i) = directionalHessian u 0 (b i) (b j) :=
    congrFun (kernelDirectionalDerivative_commute hu (b i) (b j)) 0
  have hraw := tendsto_regularized_hessian_green_pairing hu hs (b i) (b j)
  rw [hsym] at hraw
  have hαn : α < (n : ℝ) := hα1.trans_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  exact tendsto_nhds_unique hraw (tendsto_regularized_hessian_integral
    (continuous_kernelLaplacian hu) (hasCompactSupport_kernelLaplacian hs) hH hα hαn hf i j)

lemma compensatedSingularIntegral_translate (K f : KernelSpace n → ℝ) (a : KernelSpace n) :
    compensatedSingularIntegral volume K (fun y => f (y + a)) 0 =
      compensatedSingularIntegral volume K f a := by
  unfold compensatedSingularIntegral
  simp only [zero_add, zero_sub]
  have hh := integral_add_right_eq_self (μ := volume) (fun y => K (a - y) * (f y - f a)) a
  convert hh using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [show a - (x + a) = -x by module])

lemma scalarKernelConvolution_translate (K f : KernelSpace n → ℝ) (a : KernelSpace n) :
    scalarKernelConvolution volume K (fun y => f (y + a)) 0 =
      scalarKernelConvolution volume K f a := by
  unfold scalarKernelConvolution
  simp only [zero_sub]
  have hh := integral_add_right_eq_self (μ := volume) (fun y => K (a - y) * f y) a
  convert hh using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [show a - (x + a) = -x by module])

/-- Actual Hessian singular-integral representation at every point, with
all components given by the literal constructed kernels. -/
theorem compact_hessian_green_representation [NeZero n] {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasCompactSupport u) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hf : ∀ x y, |kernelLaplacian u x - kernelLaplacian u y| ≤ H * ‖x - y‖ ^ α)
    (i j : Fin n) (x : KernelSpace n) :
    (2 * (n : ℝ) * fundamentalApproxMass n) *
        directionalHessian u x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) =
      standardNewtonianSingularIntegral (kernelLaplacian u) i j x +
        (if i = j then 2 * fundamentalApproxMass n else 0) * kernelLaplacian u x +
        scalarKernelConvolution volume (standardNewtonianTail i j) (kernelLaplacian u) x := by
  let v : KernelSpace n → ℝ := fun y => u (y + x)
  have hv : ContDiff ℝ 2 v := hu.comp (contDiff_id.add contDiff_const)
  have hvs : HasCompactSupport v := hasCompactSupport_kernel_translate hs x
  have heL : kernelLaplacian v = fun y => kernelLaplacian u (y + x) := by
    funext y
    exact kernelLaplacian_comp_add_right u x y
  have hf' : ∀ y z, |kernelLaplacian v y - kernelLaplacian v z| ≤ H * ‖y - z‖ ^ α := by
    intro y z
    rw [heL]
    simpa only [add_sub_add_right_eq_sub] using hf (y + x) (z + x)
  have hh := compact_hessian_green_identity_zero hv hvs hH hα hα1 hf' i j
  have heH : directionalHessian v 0 (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) =
      directionalHessian u x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    simpa only [v, directionalHessian_comp_add_right, zero_add]
  rw [heH, heL] at hh
  simp only [zero_add, standardNewtonianSingularIntegral, compensatedSingularIntegral_translate,
    scalarKernelConvolution_translate] at hh
  exact hh

end GaussianTilt.MomentMapElliptic
