import GaussianTilt.NegativeSobolevClosable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Local energy estimates for the actual weighted elliptic operator

The Caccioppoli estimate below is derived by testing the actual weak equation
against η²h and completing squares.  It does not assume a derivative bound,
an elliptic regularity theorem, or a range-density conclusion.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma coordinateDerivative_sq_mul {n : ℕ} {η h : CoordinateSpace n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => η y ^ 2 * h y) x =
      2 * η x * coordinateDerivative i η x * h x + η x ^ 2 * coordinateDerivative i h x := by
  have hpow : (fun y => η y ^ 2) = fun y => η y * η y := by funext y; ring
  rw [coordinateDerivative_mul ((hη.pow 2).differentiable (by simp))
    (hh.differentiable (by simp)), hpow,
    coordinateDerivative_mul (hη.differentiable (by simp)) (hη.differentiable (by simp))]
  ring

/-- Pointwise square completion used in the Caccioppoli inequality. -/
lemma caccioppoli_pointwise {n : ℕ} {η h : CoordinateSpace n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hh : ContDiff ℝ ∞ h) (x : CoordinateSpace n) :
    η x ^ 2 * gradientSquare h x ≤
      2 * (∑ i, coordinateDerivative i h x *
        coordinateDerivative i (fun y => η y ^ 2 * h y) x) +
      4 * h x ^ 2 * gradientSquare η x := by
  simp only [gradientSquare, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [coordinateDerivative_sq_mul hη hh]
  nlinarith [sq_nonneg (η x * coordinateDerivative i h x +
    2 * h x * coordinateDerivative i η x)]

/-- Caccioppoli's inequality for an actual smooth weakly harmonic function.
Only the equation and compact support of the cutoff are hypotheses. -/
theorem integral_cutoff_gradientSquare_le {n : ℕ}
    (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    {h η : CoordinateSpace n → ℝ} (hh : ContDiff ℝ ∞ h)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hweak : ∀ v : CoordinateSpace n → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      (∫ x, ∑ i, coordinateDerivative i h x * coordinateDerivative i v x ∂μ) = 0) :
    (∫ x, η x ^ 2 * gradientSquare h x ∂μ) ≤
      4 * ∫ x, h x ^ 2 * gradientSquare η x ∂μ := by
  have hv := (hη.pow 2).mul hh
  have hvc : HasCompactSupport (fun x => η x ^ 2 * h x) := by
    simpa only [pow_two] using (hηc.mul_right (f' := η)).mul_right (f' := h)
  have hl : Integrable (fun x => η x ^ 2 * gradientSquare h x) μ :=
    ((hη.continuous.pow 2).mul (continuous_gradientSquare hh)).integrable_of_hasCompactSupport
      (by simpa only [pow_two] using (hηc.mul_right (f' := η)).mul_right (f' := gradientSquare h))
  have hr : Integrable (fun x => h x ^ 2 * gradientSquare η x) μ :=
    ((hh.continuous.pow 2).mul (continuous_gradientSquare hη)).integrable_of_hasCompactSupport
      (gradientSquare_hasCompactSupport hηc).mul_left
  have hm : Integrable (fun x => ∑ i, coordinateDerivative i h x *
      coordinateDerivative i (fun y => η y ^ 2 * h y) x) μ := by
    apply integrable_finset_sum
    intro i _
    exact ((smooth_coordinateDerivative hh i).continuous.mul
      (smooth_coordinateDerivative hv i).continuous).integrable_of_hasCompactSupport
        (hvc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left
  have he := integral_mono hl ((hm.const_mul 2).add (hr.const_mul 4))
    (fun x => by simpa only [Pi.add_apply, mul_assoc] using caccioppoli_pointwise hη hh x)
  simp only [Pi.add_apply] at he
  rw [integral_add (hm.const_mul 2) (hr.const_mul 4), integral_const_mul,
    integral_const_mul, hweak _ hv hvc, mul_zero, zero_add] at he
  exact he

/-- The actual weighted Laplace equation implies the weak equation used in
Caccioppoli, directly from the proved weighted Green formula. -/
theorem weightedLaplacian_zero_weak {n : ℕ} {φ h : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (hh : ContDiff ℝ ∞ h) (heq : ∀ x, weightedLaplacian φ h x = 0)
    {v : CoordinateSpace n → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    (∫ x, ∑ i, coordinateDerivative i h x * coordinateDerivative i v x
      ∂potentialMeasure φ) = 0 := by
  have hg := integral_divergenceDiffusion_mul (A := fun _ => 1)
    (contDiff_infty.mp hφ 1) (fun _ _ => contDiff_const)
    (contDiff_infty.mp hh 2) (contDiff_infty.mp hv 1) hvc
  change (∫ x, weightedLaplacian φ h x * v x ∂potentialMeasure φ) = _ at hg
  simp only [heq, zero_mul, integral_zero, diffusionGamma_one] at hg
  linarith

end GaussianTilt.Letwin
