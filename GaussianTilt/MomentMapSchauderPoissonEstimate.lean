import GaussianTilt.MomentMapEllipticFundamentalSolutionHessianRepresentation
import GaussianTilt.MomentMapSchauderHessianNorms
import GaussianTilt.MomentMapSchauderHessianInterpolation

/-!
# A genuine compact-support Poisson Schauder estimate

The exact Hessian Green representation is combined with the proved cutoff
Newtonian singular-integral estimate and the true smooth-tail estimate.
No Hessian Hölder premise or Schauder theorem is assumed.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A dimension/exponent-only entrywise Hessian Hölder estimate for an actual
compact C² solution of the Poisson equation. No C²,α premise is required. -/
theorem exists_compact_poisson_hessian_entry_holder [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : KernelSpace n → ℝ,
      ContDiff ℝ 2 u → HasCompactSupport u → ∀ F H : ℝ, 0 ≤ F → 0 ≤ H →
      (∀ x, |kernelLaplacian u x| ≤ F) →
      (∀ x y, |kernelLaplacian u x - kernelLaplacian u y| ≤ H * ‖x - y‖ ^ α) →
      ∀ (i j : Fin n) (x y : KernelSpace n), ‖x - y‖ ≤ 1 →
        |directionalHessian u x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
          directionalHessian u y (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
            C * (F + H) * ‖x - y‖ ^ α := by
  obtain ⟨Cs, hCs, hs⟩ := exists_standardNewtonianSingularIntegral_holder_bound (n := n) hα hα1
  obtain ⟨Ct, hCt, ht⟩ := exists_standardNewtonianTail_convolution_lipschitz (n := n)
  let Z : ℝ := fundamentalApproxMass n
  let N : ℝ := 2 * (n : ℝ) * Z
  have hZ : 0 < Z := fundamentalApproxMass_pos n
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hN : 0 < N := by dsimp [N]; positivity
  let C₀ : ℝ := Cs + 2 * Z + Ct
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀ / N, div_pos hC₀ hN, ?_⟩
  intro u hu huc F H hF hH hfb hfh i j x y hxy
  have hfc := GaussianTilt.MomentMapSchauder.continuous_kernelLaplacian hu
  have hfs := compactSupport_kernelLaplacian huc
  have hcore := hs (kernelLaplacian u) hfc.measurable H hH hfh i j x y
  have htail := ht (kernelLaplacian u) hfc hfs F hF hfb i j x y hxy
  have hpow : ‖x - y‖ ≤ ‖x - y‖ ^ α := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x - y)) hxy hα.le hα1.le
  have htail' := htail.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg hCt.le hF))
  have hlocal : |(if i = j then 2 * Z else 0) * (kernelLaplacian u x - kernelLaplacian u y)| ≤
      2 * Z * H * ‖x - y‖ ^ α := by
    split_ifs with hij
    · rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Z)]
      exact (mul_le_mul_of_nonneg_left (hfh x y) (by positivity)).trans_eq (by ring)
    · simp only [zero_mul, abs_zero]
      positivity
  have hxrep := compact_hessian_green_representation hu huc hH hα hα1 hfh i j x
  have hyrep := compact_hessian_green_representation hu huc hH hα hα1 hfh i j y
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have he : N * (directionalHessian u x (b i) (b j) - directionalHessian u y (b i) (b j)) =
      (standardNewtonianSingularIntegral (kernelLaplacian u) i j x -
        standardNewtonianSingularIntegral (kernelLaplacian u) i j y) +
      (if i = j then 2 * Z else 0) * (kernelLaplacian u x - kernelLaplacian u y) +
      (scalarKernelConvolution volume (standardNewtonianTail i j) (kernelLaplacian u) x -
        scalarKernelConvolution volume (standardNewtonianTail i j) (kernelLaplacian u) y) := by
    dsimp [N, Z, b]
    linarith
  have hab : N * |directionalHessian u x (b i) (b j) - directionalHessian u y (b i) (b j)| ≤
      (Cs * H + 2 * Z * H + Ct * F) * ‖x - y‖ ^ α := by
    rw [← abs_of_pos hN, ← abs_mul, he]
    exact ((abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)).trans
      ((add_le_add (add_le_add hcore hlocal) htail').trans_eq (by ring))
  have hcoeff : Cs * H + 2 * Z * H + Ct * F ≤ C₀ * (F + H) := by
    dsimp [C₀]
    nlinarith [mul_nonneg hCs.le hF, mul_nonneg (by positivity : 0 ≤ 2 * Z) hF,
      mul_nonneg hCt.le hH]
  have hab' := hab.trans (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (norm_nonneg _) _))
  calc
    _ ≤ (C₀ * (F + H) * ‖x - y‖ ^ α) / N := (le_div_iff₀ hN).mpr (by nlinarith [hab'])
    _ = _ := by ring

/-- The same true Poisson estimate in the second Fréchet-derivative norm,
with the finite-dimensional conversion proved rather than assumed. -/
theorem exists_compact_poisson_secondFrechet_holder [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : KernelSpace n → ℝ,
      ContDiff ℝ 2 u → HasCompactSupport u → ∀ F H : ℝ, 0 ≤ F → 0 ≤ H →
      (∀ x, |kernelLaplacian u x| ≤ F) →
      (∀ x y, |kernelLaplacian u x - kernelLaplacian u y| ≤ H * ‖x - y‖ ^ α) →
      ∀ x y : KernelSpace n, ‖x - y‖ ≤ 1 →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
          C * (F + H) * ‖x - y‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := exists_compact_poisson_hessian_entry_holder (n := n) hα hα1
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  refine ⟨(n : ℝ)^2 * C, by positivity, ?_⟩
  intro u hu huc F H hF hH hfb hfh x y hxy
  have he := euclidean_bilinear_norm_le_of_entries
    (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)
    (M := C * (F + H) * ‖x - y‖ ^ α) (by positivity) ?_
  · exact he.trans_eq (by ring)
  · intro i j
    simpa only [ContinuousLinearMap.sub_apply, directionalHessian_eq_secondFrechet hu] using
      hb u hu huc F H hF hH hfb hfh j i x y hxy

/-- Full global Hessian supnorm and Hölder-seminorm estimate for compact C²
Poisson solutions. The Hessian Hölder continuity is a conclusion, and its
constant depends only on dimension and exponent and the displayed data. -/
theorem exists_compact_poisson_schauder [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : KernelSpace n → ℝ,
      ContDiff ℝ 2 u → HasCompactSupport u → ∀ U F H : ℝ,
      0 ≤ U → 0 ≤ F → 0 ≤ H → (∀ x, |u x| ≤ U) →
      (∀ x, |kernelLaplacian u x| ≤ F) →
      (∀ x y, |kernelLaplacian u x - kernelLaplacian u y| ≤ H * ‖x - y‖ ^ α) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * (U + F + H)) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        C * (U + F + H) * ‖x - y‖ ^ α) := by
  obtain ⟨Ch, hCh, hh⟩ := exists_compact_poisson_secondFrechet_holder (n := n) hα hα1
  let Cs : ℝ := 16 + 2 * Ch
  let C : ℝ := 2 * Cs + Ch
  have hCs : 0 < Cs := by dsimp [Cs]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hChC : Ch ≤ C := by dsimp [C]; linarith
  have hCsC : Cs ≤ C := by dsimp [C]; linarith
  have h2CsC : 2 * Cs ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro u hu huc U F H hU hF hH hub hfb hfh
  have htotal : 0 ≤ U + F + H := by positivity
  have hsup : ∀ x : KernelSpace n, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ Cs * (U + F + H) := by
    intro x
    have hloc : ∀ y ∈ Metric.closedBall x (1 / 2 : ℝ),
        ∀ z ∈ Metric.closedBall x (1 / 2 : ℝ),
        ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ ≤
          (Ch * (F + H)) * ‖y - z‖ ^ α := by
      intro y hy z hz
      apply hh u hu huc F H hF hH hfb hfh y z
      have hy' : ‖y - x‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
      have hz' : ‖x - z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
      have ht := norm_sub_le_norm_sub_add_norm_sub y x z
      linarith
    have hi := hessian_interpolation_on_closedBall hu (x := x) (r := 1 / 2) (U := U)
      (C := Ch * (F + H)) (α := α) (by norm_num) hU (by positivity) hα.le
      (fun y _ => hub y) hloc
    norm_num at hi
    have hp : (1 / 2 : ℝ) ^ α ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hα.le
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * (Ch * (F + H)) by positivity)
    dsimp [Cs]
    nlinarith [mul_nonneg hCh.le hU]
  constructor
  · intro x
    exact (hsup x).trans (mul_le_mul_of_nonneg_right hCsC htotal)
  · intro x y
    have hp : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hxy : ‖x - y‖ ≤ 1
    · apply (hh u hu huc F H hF hH hfb hfh x y hxy).trans
      apply mul_le_mul_of_nonneg_right _ hp
      exact mul_le_mul hChC (by linarith) (by positivity) hC.le
    · have hone : (1 : ℝ) ≤ ‖x - y‖ ^ α :=
        Real.one_le_rpow (le_of_lt (lt_of_not_ge hxy)) hα.le
      have hn : ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
          2 * Cs * (U + F + H) := by
        calc
          _ ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ + ‖fderiv ℝ (fderiv ℝ u) y‖ := norm_sub_le (fderiv ℝ (fderiv ℝ u) x) (fderiv ℝ (fderiv ℝ u) y)
          _ ≤ Cs * (U + F + H) + Cs * (U + F + H) := add_le_add (hsup x) (hsup y)
          _ = _ := by ring
      apply hn.trans
      calc
        2 * Cs * (U + F + H) ≤ C * (U + F + H) := mul_le_mul_of_nonneg_right h2CsC htotal
        _ ≤ C * (U + F + H) * ‖x - y‖ ^ α := by
          exact le_mul_of_one_le_right (by positivity) hone

end GaussianTilt.MomentMapSchauder
