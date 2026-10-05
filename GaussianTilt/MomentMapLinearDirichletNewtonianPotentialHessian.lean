import GaussianTilt.MomentMapLinearDirichletNewtonianPotential

/-! # Genuine singular-integral Hessian formula for a Newtonian potential -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma newtonian_second_test_pairing [NeZero n] {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (i j : Fin n) :
    (∫ y, newtonianKernel n y * directionalHessian f y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      standardNewtonianSingularIntegral f i j 0 +
        (if i = j then 2 * fundamentalApproxMass n else 0) * f 0 +
        scalarKernelConvolution volume (standardNewtonianTail i j) f 0 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hsym (y : KernelSpace n) : directionalHessian f y (b j) (b i) = directionalHessian f y (b i) (b j) :=
    congrFun (kernelDirectionalDerivative_commute (contDiff_infty.mp hf 2) (b i) (b j)) y
  have ht := tendsto_regularizedNewtonian_test_pairing
    (continuous_directionalHessian (contDiff_infty.mp hf 2) (b i) (b j))
    ((hs.fderiv_apply ℝ (b i)).fderiv_apply ℝ (b j))
  have he : (fun c : ℝ => ∫ y, regularizedNewtonian n ((c ^ 2)⁻¹) y * directionalHessian f y (b i) (b j)) =ᶠ[atTop]
      (fun c : ℝ => ∫ y, regularizedHessianEntry ((c ^ 2)⁻¹) i j y * f y) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    have hh := integral_mul_directionalHessian_swap (contDiff_infty.mp hf 2)
      (contDiff_infty.mp (contDiff_regularizedNewtonian (n := n) (by positivity : 0 < (c ^ 2)⁻¹)) 2) hs (b i) (b j)
    simp only [hsym] at hh
    simpa only [regularizedHessianEntry, b, mul_comm] using hh.symm
  have hαn : α < (n : ℝ) := hα1.trans_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  exact tendsto_nhds_unique (ht.congr' he) (tendsto_regularized_hessian_integral hf.continuous hs hH hα hαn hholder i j)

/-- Literal Hessian representation for the actual smooth-data potential.
Unlike a compact-solution estimate, the potential need not have compact support. -/
theorem newtonianPotential_hessian_representation [NeZero n] {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (i j : Fin n) (x : KernelSpace n) :
    directionalHessian (newtonianPotential f) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) =
      standardNewtonianSingularIntegral f i j x +
        (if i = j then 2 * fundamentalApproxMass n else 0) * f x +
        scalarKernelConvolution volume (standardNewtonianTail i j) f x := by
  let v := fun y => f (y + x)
  have hv : ContDiff ℝ ∞ v := hf.comp (contDiff_id.add contDiff_const)
  have hvs := hasCompactSupport_kernel_translate hs x
  have hvh : ∀ y z, |v y - v z| ≤ H * ‖y - z‖ ^ α := by
    intro y z
    simpa only [v, add_sub_add_right_eq_sub] using hholder (y + x) (z + x)
  have hh := newtonian_second_test_pairing hv hvs hH hα hα1 hvh i j
  rw [newtonianPotential_directional_hessian hf hs, newtonianPotential_eq_add_integral]
  simpa only [v, directionalHessian_comp_add_right, zero_add,
    standardNewtonianSingularIntegral, compensatedSingularIntegral_translate,
    scalarKernelConvolution_translate] using hh

end GaussianTilt.MomentMapLinearDirichlet
