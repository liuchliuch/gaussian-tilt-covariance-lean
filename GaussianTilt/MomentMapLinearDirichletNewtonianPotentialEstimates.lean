import GaussianTilt.MomentMapLinearDirichletNewtonianPotentialHessian
import GaussianTilt.MomentMapSchauderHolderInterpolation
import GaussianTilt.MomentMapSchauderHessianNorms

/-! # Actual Hölder Hessian bounds for Newtonian potentials of compact data -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

theorem exists_newtonianPotential_hessian_entry_holder [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : KernelSpace n → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f → ∀ F H : ℝ, 0 ≤ F → 0 ≤ H →
      (∀ x, |f x| ≤ F) →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) →
      ∀ (i j : Fin n) (x y : KernelSpace n), ‖x - y‖ ≤ 1 →
        |directionalHessian (newtonianPotential f) x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
          directionalHessian (newtonianPotential f) y (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
            C * (F + H) * ‖x - y‖ ^ α := by
  obtain ⟨Cs, hCs, hs⟩ := exists_standardNewtonianSingularIntegral_holder_bound (n := n) hα hα1
  obtain ⟨Ct, hCt, ht⟩ := exists_standardNewtonianTail_convolution_lipschitz (n := n)
  let Z : ℝ := fundamentalApproxMass n
  have hZ : 0 < Z := fundamentalApproxMass_pos n
  let C₀ : ℝ := Cs + 2 * Z + Ct
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro f hf hfc F H hF hH hfb hfh i j x y hxy
  have hcore := hs (f) hf.continuous.measurable H hH hfh i j x y
  have htail := ht (f) hf.continuous hfc F hF hfb i j x y hxy
  have hpow : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x - y)) hxy hα.le hα1.le
  have htail' := htail.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg hCt.le hF))
  have hlocal : |(if i = j then 2 * Z else 0) * (f x - f y)| ≤
      2 * Z * H * ‖x - y‖ ^ α := by
    split_ifs with hij
    · rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Z)]
      exact (mul_le_mul_of_nonneg_left (hfh x y) (by positivity)).trans_eq (by ring)
    · simp only [zero_mul, abs_zero]
      positivity
  have hxrep := newtonianPotential_hessian_representation hf hfc hH hα hα1 hfh i j x
  have hyrep := newtonianPotential_hessian_representation hf hfc hH hα hα1 hfh i j y
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have he : (directionalHessian (newtonianPotential f) x (b i) (b j) - directionalHessian (newtonianPotential f) y (b i) (b j)) =
      (standardNewtonianSingularIntegral (f) i j x -
        standardNewtonianSingularIntegral (f) i j y) +
      (if i = j then 2 * Z else 0) * (f x - f y) +
      (scalarKernelConvolution volume (standardNewtonianTail i j) (f) x -
        scalarKernelConvolution volume (standardNewtonianTail i j) (f) y) := by
    dsimp [Z, b]
    linarith
  have hab : |directionalHessian (newtonianPotential f) x (b i) (b j) - directionalHessian (newtonianPotential f) y (b i) (b j)| ≤
      (Cs * H + 2 * Z * H + Ct * F) * ‖x - y‖ ^ α := by
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)).trans
      ((add_le_add (add_le_add hcore hlocal) htail').trans_eq (by ring))
  have hcoeff : Cs * H + 2 * Z * H + Ct * F ≤ C₀ * (F + H) := by
    dsimp [C₀]
    nlinarith [mul_nonneg hCs.le hF, mul_nonneg (by positivity : 0 ≤ 2 * Z) hF,
      mul_nonneg hCt.le hH]
  have hab' := hab.trans (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (norm_nonneg _) _))
  exact hab'

theorem exists_newtonianPotential_secondFrechet_holder [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : KernelSpace n → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f → ∀ F H : ℝ, 0 ≤ F → 0 ≤ H →
      (∀ x, |f x| ≤ F) →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) →
      ∀ x y : KernelSpace n, ‖x - y‖ ≤ 1 →
        ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x - fderiv ℝ (fderiv ℝ (newtonianPotential f)) y‖ ≤
          C * (F + H) * ‖x - y‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := exists_newtonianPotential_hessian_entry_holder (n := n) hα hα1
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  refine ⟨(n : ℝ)^2 * C, by positivity, ?_⟩
  intro f hf hfc F H hF hH hfb hfh x y hxy
  have he := euclidean_bilinear_norm_le_of_entries
    (fderiv ℝ (fderiv ℝ (newtonianPotential f)) x - fderiv ℝ (fderiv ℝ (newtonianPotential f)) y)
    (M := C * (F + H) * ‖x - y‖ ^ α) (by positivity) ?_
  · exact he.trans_eq (by ring)
  · intro i j
    simpa only [ContinuousLinearMap.sub_apply, directionalHessian_eq_secondFrechet (contDiff_infty.mp (smooth_newtonianPotential hf hfc) 2)] using
      hb f hf hfc F H hF hH hfb hfh j i x y hxy

end GaussianTilt.MomentMapLinearDirichlet
